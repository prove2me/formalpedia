-- Prove2me | Theorems.Thm_OpenSearchPreVote_round_entries
-- name    : OpenSearchPreVote.round_entries
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:35:41.035139+00:00
-- url     : https://prove2.me/theorems/3b90bc21-eac4-475c-b0f0-e0d4e7e553b6
-- title:
--   A round records only no-fresher, delivered responses, one per sender
-- statement:
--   For every election strategy `es`, delivery predicate `Delivered` and round `r` with `RoundReachable es Delivered r` (started, then any responses allowed by `Delivered` handled in any order and any number of times, and possibly closed):
--
--   - every recorded entry `p ∈ r.preVotesReceived` satisfies `NoFresher p.2 r.clusterState` — the response's accepted (term, version) is lexicographically at most the round's accepted (term, version-or-metadata-version) — and `Delivered p.1 p.2`;
--   - the senders of the recorded entries are pairwise distinct as node values (id and role; two entries may share an id with different roles): `(r.preVotesReceived.map Prod.fst).Nodup`.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: PreVoteCollector (state line 79, start 111-115, update 128-131, handlePreVoteRequest 133-163, PreVotingRound 175-300, handlePreVoteResponse 225-279, close 296-299): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PreVoteCollector.java#L66-L301; Coordinator (updateMaxTermSeen lines 560-581, startElection 583-602, nodeMayWinElection 628-633, getPreVoteResponse 873-879, handleJoin 1267-1299, startElectionScheduler 1567-1618, the preVoteCollector.update calls 516, 653, 777, 801, 839, 1157): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L560-L633; ElectionSchedulerFactory (settings lines 85-115, constructor check 133-143, nonNegative 159-161, toPositiveLongAtMost 169-172, scheduleNextElection 195-241): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; ElectionStrategy.isElectionQuorum (lines 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L68-L88; the messages PreVoteRequest.java and PreVoteResponse.java in the same directory; CoordinationState (handleStartJoin, handleJoin) as transcribed by the OpenSearchCoordination mission

import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.round_entries {V : Type} (es : ElectionStrategy)
    (Delivered : DiscoveryNode → PreVoteResponse → Prop) (r : PreVotingRound V)
    (hr : RoundReachable es Delivered r) :
    (∀ p ∈ r.preVotesReceived, NoFresher p.2 r.clusterState ∧ Delivered p.1 p.2) ∧
    (r.preVotesReceived.map Prod.fst).Nodup := by sorry
