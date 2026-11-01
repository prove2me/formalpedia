-- Prove2me | Theorems.Thm_OpenSearchPreVote_handlePreVoteRequest_spec
-- name    : OpenSearchPreVote.handlePreVoteRequest_spec
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:35:16.06983+00:00
-- url     : https://prove2.me/theorems/4892d061-2ffa-4359-beeb-1c36fd9d298a
-- title:
--   A node answers a pre-vote request exactly when it is healthy and follows no other leader
-- statement:
--   For every health status `healthy`, collector state `st`, request `req` and response `resp`: `handlePreVoteRequest healthy st req = .ok resp` iff `healthy = true`, the node knows no leader or knows the requester as its leader (`st.leader = none ∨ st.leader = some req.sourceNode`), and `resp = st.response`, the node's own current response. Unhealthy nodes and nodes that follow a leader other than the requester refuse.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: PreVoteCollector (state line 79, start 111-115, update 128-131, handlePreVoteRequest 133-163, PreVotingRound 175-300, handlePreVoteResponse 225-279, close 296-299): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PreVoteCollector.java#L66-L301; Coordinator (updateMaxTermSeen lines 560-581, startElection 583-602, nodeMayWinElection 628-633, getPreVoteResponse 873-879, handleJoin 1267-1299, startElectionScheduler 1567-1618, the preVoteCollector.update calls 516, 653, 777, 801, 839, 1157): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L560-L633; ElectionSchedulerFactory (settings lines 85-115, constructor check 133-143, nonNegative 159-161, toPositiveLongAtMost 169-172, scheduleNextElection 195-241): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; ElectionStrategy.isElectionQuorum (lines 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L68-L88; the messages PreVoteRequest.java and PreVoteResponse.java in the same directory; CoordinationState (handleStartJoin, handleJoin) as transcribed by the OpenSearchCoordination mission

import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.handlePreVoteRequest_spec (healthy : Bool) (st : CollectorState) (req : PreVoteRequest)
    (resp : PreVoteResponse) :
    handlePreVoteRequest healthy st req = .ok resp ↔
      healthy = true ∧ (st.leader = none ∨ st.leader = some req.sourceNode) ∧ resp = st.response := by sorry
