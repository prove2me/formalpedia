-- Prove2me | Theorems.Thm_OpenSearchPreVote_round_start_quorum
-- name    : OpenSearchPreVote.round_start_quorum
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:35:51.313501+00:00
-- url     : https://prove2.me/theorems/4fb9cb61-97f2-4e4e-8590-ce3d5612c67e
-- title:
--   A round starts an election only on an election quorum, only while open and not yet started
-- statement:
--   For every election strategy `es`, requester response `lr`, response `resp`, sender, rounds `r` and `r'` and `m`: if `r.handlePreVoteResponse es lr resp sender = (r', true, m)` — handling the response calls `startElection` — then
--
--   - `r.isClosed = false`, `r.electionStarted = false` and `r'.electionStarted = true`;
--   - `NoFresher resp r.clusterState`;
--   - `r'` has the accepted state and the local node of `r`;
--   - the votes of `r'`, the round as updated by the response, form an election quorum for the round's local node and the requester's response `lr` over the last committed and last accepted configurations of the round's accepted state: `isElectionQuorumFor es r.localNode lr.currentTerm lr.lastAcceptedTerm lr.lastAcceptedVersion r.clusterState.lastCommittedConfiguration r.clusterState.lastAcceptedConfiguration r'.votes = true`.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: PreVoteCollector (state line 79, start 111-115, update 128-131, handlePreVoteRequest 133-163, PreVotingRound 175-300, handlePreVoteResponse 225-279, close 296-299): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PreVoteCollector.java#L66-L301; Coordinator (updateMaxTermSeen lines 560-581, startElection 583-602, nodeMayWinElection 628-633, getPreVoteResponse 873-879, handleJoin 1267-1299, startElectionScheduler 1567-1618, the preVoteCollector.update calls 516, 653, 777, 801, 839, 1157): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L560-L633; ElectionSchedulerFactory (settings lines 85-115, constructor check 133-143, nonNegative 159-161, toPositiveLongAtMost 169-172, scheduleNextElection 195-241): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; ElectionStrategy.isElectionQuorum (lines 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L68-L88; the messages PreVoteRequest.java and PreVoteResponse.java in the same directory; CoordinationState (handleStartJoin, handleJoin) as transcribed by the OpenSearchCoordination mission

import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.round_start_quorum {V : Type} (es : ElectionStrategy) (lr resp : PreVoteResponse)
    (sender : DiscoveryNode) (r r' : PreVotingRound V) (m : Option Nat)
    (h : r.handlePreVoteResponse es lr resp sender = (r', true, m)) :
    r.isClosed = false ∧ r.electionStarted = false ∧ r'.electionStarted = true ∧ NoFresher resp r.clusterState ∧
    r'.clusterState = r.clusterState ∧ r'.localNode = r.localNode ∧
    isElectionQuorumFor es r.localNode lr.currentTerm lr.lastAcceptedTerm lr.lastAcceptedVersion
      r.clusterState.lastCommittedConfiguration r.clusterState.lastAcceptedConfiguration r'.votes = true := by sorry
