package collabai.group21;

import java.io.IOException;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.*;
import java.util.logging.Level;
import java.util.stream.Collectors;

import geniusweb.actions.Accept;
import geniusweb.actions.Action;
import geniusweb.actions.Offer;
import geniusweb.actions.PartyId;
import geniusweb.actions.Vote;
import geniusweb.actions.Votes;
import geniusweb.exampleparties.timedependentparty.ExtendedUtilSpace;
import geniusweb.inform.*;
import geniusweb.issuevalue.*;
import geniusweb.party.Capabilities;
import geniusweb.party.DefaultParty;
import geniusweb.profile.Profile;
import geniusweb.profile.utilityspace.DiscreteValueSetUtilities;
import geniusweb.profile.utilityspace.LinearAdditive;
import geniusweb.profile.utilityspace.LinearAdditiveUtilitySpace;
import geniusweb.profile.utilityspace.ValueSetUtilities;
import geniusweb.profileconnection.ProfileConnectionFactory;
import geniusweb.profileconnection.ProfileInterface;
import geniusweb.progress.Progress;
import geniusweb.progress.ProgressRounds;
import tudelft.utilities.immutablelist.ImmutableList;
import tudelft.utilities.logging.Reporter;
import geniusweb.opponentmodel.FrequencyOpponentModel;

/**
 * A simple party that places random bids and accepts when it receives an offer
 * with sufficient utility.
 * <h2>parameters</h2>
 * <table >
 * <caption>parameters</caption>
 * <tr>
 * <td>minPower</td>
 * <td>This value is used as minPower for placed {@link Vote}s. Default value is
 * 2.</td>
 * </tr>
 * <tr>
 * <td>maxPower</td>
 * <td>This value is used as maxPower for placed {@link Vote}s. Default value is
 * infinity.</td>
 * </tr>
 * </table>
 */
public class Group21Party extends DefaultParty {


    private Bid lastReceivedBid = null;
    private ExtendedUtilSpace extendedUtilSpace;
    private LinearAdditive utilspace = null;
    private Bid lastSentBid = null;
    private PartyId me;
    protected ProfileInterface profileint;
    private Progress progress;
    private Settings settings;
    private Votes lastvotes;
    private String protocol;
    private int currentRound = 0;
    private double opponentsDelta = 0;
    private double ourDelta = 0;
    private final List<Bid> opponentsBids = new ArrayList<>();
    private final List<Bid> ourBids = new ArrayList<>();
    private final List<Move> opponentsMoves = new ArrayList<>();
    private FrequencyOpponentModel opponentModel = new FrequencyOpponentModel();
    private final Map<Move, Integer> moveCounter = new HashMap<>();
    private double reservationValue = 0.7; // TODO Set it to the value of the reservation bid somehow.
    private BigDecimal ourUtil = new BigDecimal("0.8");
    private BigDecimal theirUtil = new BigDecimal("0.4");

    public Group21Party() {
    }

    public Group21Party(Reporter reporter) {
        super(reporter); // for debugging

    }

    @Override
    public void notifyChange(Inform info) {
        try {
            if (info instanceof Settings) {
                Settings settings = (Settings) info;
                this.profileint = ProfileConnectionFactory
                        .create(settings.getProfile().getURI(), getReporter());
                this.me = settings.getID();
                this.progress = settings.getProgress();
                this.settings = settings;
                this.protocol = settings.getProtocol().getURI().getPath();

                LinearAdditiveUtilitySpace space = (LinearAdditiveUtilitySpace) profileint.getProfile();
                Map<String, ValueSetUtilities> valueutils = space.getUtilities();

                for (String issue : space.getDomain().getIssues()) {
                    System.out.println(">>" + issue + " weight : " + space.getWeight(issue));
                    ValueSetUtilities utils = valueutils.get(issue); // ignore the non−discrete in this demo
                    if (!(utils instanceof DiscreteValueSetUtilities)) continue;
                    Map<DiscreteValue, BigDecimal> values = ((DiscreteValueSetUtilities) utils).getUtilities();
                    for (DiscreteValue value : values.keySet()) {
                        System.out.println("utility( " + value + ")=" + values.get(value));
                    }
                }

            } else if (info instanceof ActionDone) {
                Action otheract = ((ActionDone) info).getAction();
                if (otheract instanceof Offer) {

                    lastReceivedBid = ((Offer) otheract).getBid();
                    try {
                        opponentsDelta = getOpponentsUtilBasedOnBid(lastReceivedBid) - getOpponentsUtilBasedOnBid(opponentsBids.get(opponentsBids.size() - 1));
                    } catch (IndexOutOfBoundsException e) {
                        opponentsDelta = getOpponentsUtilBasedOnBid(lastReceivedBid);
                    }

                    try {
                        ourDelta = 0.01;

                        if (lastReceivedBid != null && opponentsBids.size() != 0)
                            ourDelta = getOurUtility(lastReceivedBid) - getOurUtility(opponentsBids.get(opponentsBids.size() - 1));

                    } catch (IndexOutOfBoundsException e) {
                        ourDelta = 0.01;
                        if (lastReceivedBid != null) ourDelta = getOurUtility(lastReceivedBid);
                    }
                    //Adding opponent's action, updating their preference model and move counter
                    opponentsBids.add(lastReceivedBid);
                    opponentsMoves.add(classifyMove());
                    updateOpponentPreferenceModel(otheract);
                    updateMoveCounter();
                }
            } else if (info instanceof YourTurn) {
                makeOffer();
            } else if (info instanceof Finished) {
                getReporter().log(Level.INFO, "Final outcome:" + info);
            } else if (info instanceof Voting) {
                lastvotes = vote((Voting) info);
                getConnection().send(lastvotes);
            } else if (info instanceof OptIn) {
                // just repeat our last vote.
                getConnection().send(lastvotes);
            }
        } catch (Exception e) {
            throw new RuntimeException("Failed to handle info..." ,e);
        }

        updateRound(info);
        //Updating round to be used with the isGood method
        currentRound++;
    }

    @Override
    public Capabilities getCapabilities() {
        return new Capabilities(
                new HashSet<>(Arrays.asList("SAOP", "AMOP", "MOPAC")),
                Collections.singleton(Profile.class));
    }

    @Override
    public String getDescription() {
        return "Agent negotiates according to a modified Tit-for-Tat strategy. "+
                "Then accepts bids that are either accepted by ACNext and, hence, their utility is better than ours" +
                " or by ACTime which means that 175 rounds have passed and the bid is simply better or equal to our reservation bid";
    }

    /**
     * Update {@link #progress}
     *
     * @param info the received info. Used to determine if this is the last info
     *             of the round
     */
    private void updateRound(Inform info) {
        if (protocol == null)
            return;
        switch (protocol) {
            case "SAOP":
            case "SHAOP":
                if (!(info instanceof YourTurn))
                    return;
                break;
            case "MOPAC":
                if (!(info instanceof OptIn))
                    return;
                break;
            default:
                return;
        }
        // if we get here, round must be increased.
        if (progress instanceof ProgressRounds) {
            progress = ((ProgressRounds) progress).advance();
        }

    }

    /**
     * Sending our next offer to the opponent and updating our utility space.
     * If our makeBid() method fails to construct a bid the reservation bid is selected to be sent.
     * Also, if the opponent's last bid was accepted by isGood() we accept it and end the negotiation.
     * @throws IOException
     */
    private void makeOffer() throws IOException {
        Action action;
        updateUtilSpace();
        Bid bid = makeBid();

        if ((protocol.equals("SAOP") || protocol.equals("SHAOP"))
                && isGood(lastReceivedBid, bid)) {
            action = new Accept(me, lastReceivedBid);
        } else {
            if (!isOurBidGood(bid))
                bid = utilspace.getReservationBid();

            action = new Offer(me, bid);
            lastSentBid = bid;
            ourBids.add(bid);
        }
        if(action == null)
            action = new Accept(me, lastReceivedBid);
        getConnection().send(action);
    }

    /**
     * @param voting the {@link Voting} object containing the options
     * @return our next Votes.
     */
    private Votes vote(Voting voting) {
        Object val = settings.getParameters().get("minPower");
        Integer minpower = (val instanceof Integer) ? (Integer) val : 2;
        val = settings.getParameters().get("maxPower");
        Integer maxpower = (val instanceof Integer) ? (Integer) val
                : Integer.MAX_VALUE;

        Set<Vote> votes = voting.getBids().stream().distinct()
                .filter(offer -> {
                    return isGood(offer.getBid(), null);
                })
                .map(offer -> new Vote(me, offer.getBid(), minpower, maxpower))
                .collect(Collectors.toSet());
        return new Votes(me, votes);
    }


    /**
     * Updating util space and setting reservation value. Some reservation bids are interpreted as having utility of 0.
     * Hence, 0.6 is a value we chose to replace the reservation value for those exceptional cases. (A bid with lower utility
     * could still be accepted in ACTime after 175 rounds).
     * @return the updated utility space
     * @throws IOException
     */
    private LinearAdditive updateUtilSpace() throws IOException {
        Profile newutilspace = profileint.getProfile();
        if (!newutilspace.equals(utilspace)) {
            utilspace = (LinearAdditive) newutilspace;
            extendedUtilSpace = new ExtendedUtilSpace(utilspace);
        }

        reservationValue = getOurUtility(utilspace.getReservationBid());
        if(reservationValue <= 0.01){
            reservationValue = 0.6;
        }

        return utilspace;
    }

    /**
     *  Make bid produces the next bid to be offered to the opponent. It uses the logic for determining what type of move the next bid will be.
     *  It also prioritizes this agent's utility goal (which is determined based on the move) over the opponent's.
     * @return bid to be offered to the opponent
     */
    private Bid makeBid() {
        Move move = getOurNextMove();
        Goal[] goals = ourMoveToGoalForBoth(move);
        BigDecimal ourUtilityGoal = getUtilityGoalForUs(goals[0]);
        BigDecimal theirUtilityGoal = getUtilityGoalForThem(goals[1]);
        //This is where the bid is selected. Get bids has some tolerance so bids close to our goal will be selected.
        ImmutableList<Bid> options = extendedUtilSpace.getBids(ourUtilityGoal);
        if (options.size().equals(BigInteger.ZERO)) {
            // if we can't find good bid, get max util bid....
            options = extendedUtilSpace.getBids(extendedUtilSpace.getMax());
        }

        List<Bid> bidsForBoth = new ArrayList<>();
        for (Bid bid : options) {
            double opponentsutil = getOpponentsUtilBasedOnBid(bid);
            if (opponentsutil == -1)
                continue;
            if (opponentsutil < theirUtilityGoal.doubleValue() && opponentsutil > theirUtilityGoal.subtract(BigDecimal.valueOf(0.1)).doubleValue())
                bidsForBoth.add(bid);
        }

        if (bidsForBoth.size() != 0)
            return bidsForBoth.get(new Random().nextInt(bidsForBoth.size()));
        else
            return options.get(new Random().nextInt(options.size().intValue()));
    }

    /**
     * Get utility goal produces the ideal utility for the next bid based on the current utility and ourGoal
     * @param ourGoal determines whether the agent will increase or decrease utility
     * @return the ideal utility of our agent for the next bid
     */
    private BigDecimal getUtilityGoalForUs(Goal ourGoal) {
        double OUR_INC_CONSTANT = 0.07;
        double OUR_DEC_CONSTANT = 0.04;

        double[] ourConstants = getOurConstants();

        if (ourConstants != null) {
            OUR_INC_CONSTANT = ourConstants[0];
            OUR_DEC_CONSTANT = ourConstants[1];
        }


        if (ourGoal == Goal.INCREASE)
            ourUtil = ourUtil.add(BigDecimal.valueOf(OUR_INC_CONSTANT));
        else
            ourUtil = ourUtil.subtract(BigDecimal.valueOf(OUR_DEC_CONSTANT));

        //If increase or decrease produces a goal out of the boundaries determined by the reservation value
        //then the value is set to one within those boundaries (one is the maximum and the reservation value is the minimum)
        ourUtil = (ourUtil.doubleValue() <= 1) ? ourUtil : BigDecimal.ONE;
        ourUtil = (ourUtil.doubleValue() > reservationValue) ? ourUtil : BigDecimal.valueOf(reservationValue);

        return ourUtil;
    }

    /**
     * Same as getUtilityGoalForUs but determining opponent's ideal utility for the next bid.
     * @param theirGoal determines whether the agent will increase or decrease utility for opponent
     * @return the ideal utility of the opponent for the next bid
     */
    private BigDecimal getUtilityGoalForThem(Goal theirGoal) {
        double THEIR_INC_CONSTANT = 0.03;
        double THEIR_DEC_CONSTANT = 0.08;

        double[] theirConstants = getTheirConstants();

        if (theirConstants != null) {
            THEIR_INC_CONSTANT = theirConstants[0];
            THEIR_DEC_CONSTANT = theirConstants[1];
        }

        if (theirGoal == Goal.INCREASE)
            theirUtil = theirUtil.add(BigDecimal.valueOf(THEIR_INC_CONSTANT));
        else
            theirUtil = theirUtil.subtract(BigDecimal.valueOf(THEIR_DEC_CONSTANT));

        theirUtil = (theirUtil.doubleValue() > 0.1) ? theirUtil : BigDecimal.valueOf(0.1001);
        return theirUtil;
    }

    /**
     * Produces constants that determine ideal increase or decrease that will be used to calculate ideal utility of the next bid for this agent.
     * These constants are also modified by a selfishnessTax, which is making sure the agent acts a little more selfishly per move.
     * @return double array with the two constants
     */
    private double[] getOurConstants() {

        double[] result = new double[2];

        if (lastReceivedBid == null || lastSentBid == null)
            return null;

        double sum = ourBids.stream().mapToDouble(this::getOurUtility).sum();
        double avg = sum / ourBids.size();

        double previousSentUtil = getOurUtility(lastSentBid);

        double selfishnessTax = (isSelfish()) ? 0.1 : -0.001; // subtract it from decrease and add it to increase

        double increase;
        double decrease;

        double distFromReservationValue = previousSentUtil - reservationValue;

        if (previousSentUtil < avg) {
            // Linearly while taking into consideration avg- previousSentUtil and also the distance from the reservationValue
            double difference = avg - previousSentUtil;
            double toAdd = (distFromReservationValue != 0) ? (1 / distFromReservationValue) % 0.2 : 0.2;

            difference *= 10; // Make it an int;

            increase = decrease = difference % 0.15 + toAdd;
        } else {
            double difference = previousSentUtil - avg;

            difference *= 5;
            increase = decrease = difference % 0.07;

        }

        result[0] = increase + selfishnessTax;
        result[1] = decrease - selfishnessTax;

        return result;
    }

    /**
     * Produces constants that determine ideal increase or decrease that will be used to calculate ideal utility of the next bid for the opponent.
     * These constants are also modified by a selfishnessTax, which is making sure the agent acts a little more selfishly per move,
     * if the opponent also acted selfishly in their last bid.
     * @return double array with the two constants
     */
    private double[] getTheirConstants() {
        // [0] Increase
        // [1] Decrease
        double[] result = new double[2];

        if (lastReceivedBid == null || lastSentBid == null)
            return null;
        double[] utils = opponentsBids.stream().mapToDouble(this::getOurUtility).toArray();

        if (utils.length < 2)
            return null;

        double sumOfDeltas = 0;
        for (int i = 1; i < utils.length; i++) {
            double delta = utils[i] - utils[i - 1];
            sumOfDeltas += delta;
        }
        if (sumOfDeltas == 0)
            return null;

        double averageDelta = sumOfDeltas / utils.length;

        double selfishnessTax = (isSelfish()) ? 0.05 : 0.001; // add it in decrease and subtract it from increase

        result[1] = averageDelta - (ourDelta % 0.05) + selfishnessTax; // If he was good with us the number that we will decrease his util with will be lower, else higher
        result[0] = averageDelta + (ourDelta % 0.05) - selfishnessTax;  // If he was good with us, the number that we will increase his util with will be higher else lower
        // Modding is to add a randomness

        return result;
    }

    /**
     *
     * @param move
     * @return
     */
    private Goal[] ourMoveToGoalForBoth(Move move) {
        Goal[] result = new Goal[2];
        // [0] is us
        // [1] is them
        switch (move) {
            case CONCESSION:
                result[0] = Goal.DECREASE;
                result[1] = Goal.INCREASE;
                break;
            case FORTUNATE:
                result[0] = Goal.INCREASE;
                result[1] = Goal.INCREASE;
                break;
            case UNFORTUNATE:
            case SELFISH:
                result[0] = Goal.INCREASE;
                result[1] = Goal.DECREASE;
                break;
        }
        return result;
    }

    /**
     * Determines whether opponent's bid should be accepted based on ACNext() and ACTime() criteria.
     * @param oppBid the opponent's bid
     * @param ourBid this agent's bid
     * @return whether bid should be accepted or not
     */
    private boolean isGood(Bid oppBid, Bid ourBid) {

        if (oppBid == null || ourBid == null)
            return false;

        //After 175, use ACTime
        if (currentRound < 175)
            return ACNext(oppBid, ourBid);
        else
            return ACTime();

    }

    /**
     * Determines whether this agent's bid qualifies to be offered to the opponent. Only criterion is having a utility
     * higher than the reservation bid
     * @param bid the bid to be evaluated.
     * @return whether bid qualifies to be offered
     */
    private boolean isOurBidGood(Bid bid){

        if(bid == null){
            return false;
        }

        return getOurUtility(bid) >= getOurUtility(utilspace.getReservationBid());
    }

    /**
     * Returns true if the utility offered by this agent's next planned bid is lower than the utility calculated from the opponent's offer.
     * @param oppBid the opponents bid
     * @param ourBid this agent's
     * @return true or false
     */
    private boolean ACNext(Bid oppBid, Bid ourBid) {

        // if our next bid  is lower or equal to last received bid, accept. Else continue
        return getOurUtility(ourBid) <= getOurUtility(oppBid);
    }

    /**
     * Returns true iff the last received bid from the opponent's has a higher utility than the minimum utility allowed.
     * This minimum utility decreases linearly depending on the round of the negotiation until it reaches the value of the reservation bid.
     * @return true or false
     */
    private boolean ACTime() {

        double minimumUtility = getOurUtility(utilspace.getReservationBid());

        minimumUtility += (200 - currentRound) * 0.005;

        return minimumUtility
                <= getOurUtility(lastReceivedBid);

    }

    /**
     * Determines our next move based on the opponent's last move. If the negotiation is within the first 20 rounds the move is the same as the opponent's.
     * For the rest of the negotiation, if the move made was by mistake (since the opponent model we use to determine the type of move made is only an approximation)
     * then we simply act in an absolut Tit-for-Tat manner and mirror their move.
     * If the move was not made by mistake then if the move was an unfortunate one our next move will be fortunate. If the move was a selfish one then if the
     * opponent is classified as selfish (by isSelfish()) the agent also responds with a selfish move, otherwise with a fortunate one.
     * @return the type of move the agent will make.
     */
    private Move getOurNextMove() {
        Move lastMove = lastOpponentMove();
        // If it is too early just model
        if (currentRound <= 20)
            return lastMove;

        if (!isByMistake(lastMove)) {
            switch (lastMove) {
                case UNFORTUNATE:
                    return Move.FORTUNATE;
                case SELFISH:
                    if (isSelfish())
                        return Move.SELFISH;
                    else
                        return Move.FORTUNATE;
                default:
                    return lastMove;
            }
        } else {
            return lastMove;
        }
    }

    /**
     * Determined if a move was classified by "mistake". This could have arisen from the opponent model not being completely accurate
     * to the opponent's utility function.
     * @param move that was made
     * @return true or false
     */
    private boolean isByMistake(Move move) {
        if (moveCounter.get(move) <= 2)
            return true;

        return moveCounter.get(move) < currentRound / 12;
    }

    private void updateMoveCounter() {
        Move lastMove = lastOpponentMove();
        moveCounter.put(lastMove, moveCounter.getOrDefault(lastMove, 1));
    }

    /**
     * If the opponent has made a SELFISH move for more than a 16th of their moves they are classified as selfish.
     * @return true if they are selfish.
     */
    private boolean isSelfish() {

        int count = moveCounter.getOrDefault(Move.SELFISH, 0);

        return count > opponentsMoves.size() / 16; //16 could be optimized
    }

    /**
     * Returns the last move made by the opponent
     * @return Move
     */
    private Move lastOpponentMove() {
        if (opponentsMoves.size() == 0) {
            return Move.SELFISH;
        }
        return opponentsMoves.get(opponentsMoves.size() - 1);
    }

    /**
     * Calculates utility of bid based on opponent model constructed by the agent.
     * @param bid
     * @return double utility
     */
    private double getOpponentsUtilBasedOnBid(Bid bid) {
        try {
            return opponentModel.getUtility(bid).doubleValue();
        } catch (IllegalStateException e) {
            return -1;
        }

    }

    /**
     * Method to classify the current move made by the opponent
     *
     * @return The move of the opponent
     */
    private Move classifyMove() {
        if (ourDelta > 0 && opponentsDelta < 0)
            return Move.CONCESSION;
        else if (ourDelta < 0 && opponentsDelta < 0)
            return Move.UNFORTUNATE;
        else if (ourDelta < 0 && opponentsDelta > 0)
            return Move.SELFISH;
        else
            return Move.FORTUNATE;
    }

    private double getOurUtility(Bid bid) {

        return utilspace.getUtility(bid).doubleValue();
    }

    /**
     * Updates this agent's model of the opponent's utility function based on the action (offer) made by the opponent.
     * @param action
     */
    private void updateOpponentPreferenceModel(Action action) {
        if (opponentModel.getDomain() == null) {

            if(utilspace == null)
                return;

            opponentModel = opponentModel.with(utilspace.getDomain(), lastReceivedBid); // Find which bid probably represents his reservation bid
        } else
            opponentModel = opponentModel.with(action, progress);
    }
}

enum Move {
    CONCESSION,
    UNFORTUNATE,
    SELFISH,
    FORTUNATE
}

enum Goal {
    INCREASE,
    DECREASE
}
