-- Prove2me | Theorems.Thm_OpenSearchPreVote_votes_mem
-- name    : OpenSearchPreVote.votes_mem
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:35:30.307343+00:00
-- url     : https://prove2.me/theorems/884e19e9-fff4-4eca-aa59-115292f92b9d
-- title:
--   A round counts exactly its cluster-manager-eligible senders
-- statement:
--   For every pre-voting round `r` and node id `x`: `x` is among the ids of `r.votes` iff some recorded entry `p ∈ r.preVotesReceived` has `p.1.id = x` and `p.1.isClusterManagerNode = true`. The votes of a round are the ids of its recorded senders that have the cluster-manager role.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: PreVoteCollector (state line 79, start 111-115, update 128-131, handlePreVoteRequest 133-163, PreVotingRound 175-300, handlePreVoteResponse 225-279, close 296-299): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PreVoteCollector.java#L66-L301; Coordinator (updateMaxTermSeen lines 560-581, startElection 583-602, nodeMayWinElection 628-633, getPreVoteResponse 873-879, handleJoin 1267-1299, startElectionScheduler 1567-1618, the preVoteCollector.update calls 516, 653, 777, 801, 839, 1157): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L560-L633; ElectionSchedulerFactory (settings lines 85-115, constructor check 133-143, nonNegative 159-161, toPositiveLongAtMost 169-172, scheduleNextElection 195-241): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; ElectionStrategy.isElectionQuorum (lines 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L68-L88; the messages PreVoteRequest.java and PreVoteResponse.java in the same directory; CoordinationState (handleStartJoin, handleJoin) as transcribed by the OpenSearchCoordination mission

import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.votes_mem {V : Type} (r : PreVotingRound V) (x : NodeId) :
    x ∈ r.votes.nodes ↔ ∃ p ∈ r.preVotesReceived, p.1.id = x ∧ p.1.isClusterManagerNode = true := by sorry
