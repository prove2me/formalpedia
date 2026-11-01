-- Prove2me | Theorems.Thm_OpenSearchPreVote_nonNegative_two_to_one
-- name    : OpenSearchPreVote.nonNegative_two_to_one
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:36:46.074418+00:00
-- url     : https://prove2.me/theorems/4e502ad2-eb9e-430a-b6b7-9d80db32dcc9
-- title:
--   nonNegative maps the Java longs exactly two-to-one onto [0, 2^63)
-- statement:
--   For every natural number $v < 2^{63}$ and every integer $n$ with $-2^{63} \le n < 2^{63}$ (a Java `long`): `nonNegative n = v` iff $n = v$, or $n = -v$ when $v > 0$, respectively $n = -2^{63}$ (`Long.MIN_VALUE`) when $v = 0$. Every value in $[0, 2^{63})$ has exactly two preimages among the $2^{64}$ longs, so a uniformly distributed long gives a uniformly distributed `nonNegative` value. The theorem is the counting statement; no probability is formalized.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: PreVoteCollector (state line 79, start 111-115, update 128-131, handlePreVoteRequest 133-163, PreVotingRound 175-300, handlePreVoteResponse 225-279, close 296-299): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PreVoteCollector.java#L66-L301; Coordinator (updateMaxTermSeen lines 560-581, startElection 583-602, nodeMayWinElection 628-633, getPreVoteResponse 873-879, handleJoin 1267-1299, startElectionScheduler 1567-1618, the preVoteCollector.update calls 516, 653, 777, 801, 839, 1157): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L560-L633; ElectionSchedulerFactory (settings lines 85-115, constructor check 133-143, nonNegative 159-161, toPositiveLongAtMost 169-172, scheduleNextElection 195-241): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; ElectionStrategy.isElectionQuorum (lines 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L68-L88; the messages PreVoteRequest.java and PreVoteResponse.java in the same directory; CoordinationState (handleStartJoin, handleJoin) as transcribed by the OpenSearchCoordination mission

import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.nonNegative_two_to_one (v : Nat) (hv : v < 2 ^ 63) (n : Int)
    (hn : -2 ^ 63 ≤ n ∧ n < 2 ^ 63) :
    nonNegative n = v ↔ n = v ∨ n = (if v = 0 then -2 ^ 63 else -(v : Int)) := by sorry
