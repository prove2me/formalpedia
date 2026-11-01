-- Prove2me | Theorems.Thm_OpenSearchPreVote_no_disruption
-- name    : OpenSearchPreVote.no_disruption
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:36:10.022934+00:00
-- url     : https://prove2.me/theorems/569a49a0-1d8d-4c96-aa6a-3f8cda774006
-- title:
--   A pre-voting round that a quorum refuses never starts an election
-- statement:
--   Fix an election strategy `es`, the health `healthy n` and collector state `st n` of every node `n` (as they stand while the round runs), a requester `c` whose pre-vote requests carry the term `t`, a cluster state `s`, and a list of node ids `L` that is a quorum of the last committed or of the last accepted configuration of `s`. Suppose every node whose id is in `L` is unhealthy or knows a leader other than `c`: for every `n` with `n.id ∈ L`, `healthy n = false`, or `(st n).leader = some l` with `l ≠ c`. Let `r` be a round over `s` (`r.clusterState = s`) that is reachable when the deliverable responses are exactly the answers to `c`'s request, `handlePreVoteRequest (healthy n) (st n) ⟨c, t⟩ = .ok resp`. Then `r.electionStarted = false`, and handling any further such answer, with any requester response `lr`, does not call `startElection`.
--
--   Whatever answers arrive, in whatever order and number: only nodes outside `L` answer, and a set of voters disjoint from a quorum of a configuration is not a quorum of it, so the election-quorum test, which needs quorums of both configurations, never passes. A node cut off from a cluster whose majority follows a leader cannot depose that leader by starting elections when it reconnects. The theorem does not cover the requests' side effect: each request raises the receiver's largest seen term to at least `t`, and a leader whose current term is below `t` then moves to that larger term and starts an election itself, immediately or after its publication in progress (`Coordinator.updateMaxTermSeen`, CO:560-581, and CO:1784).
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: PreVoteCollector (state line 79, start 111-115, update 128-131, handlePreVoteRequest 133-163, PreVotingRound 175-300, handlePreVoteResponse 225-279, close 296-299): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PreVoteCollector.java#L66-L301; Coordinator (updateMaxTermSeen lines 560-581, startElection 583-602, nodeMayWinElection 628-633, getPreVoteResponse 873-879, handleJoin 1267-1299, startElectionScheduler 1567-1618, the preVoteCollector.update calls 516, 653, 777, 801, 839, 1157): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L560-L633; ElectionSchedulerFactory (settings lines 85-115, constructor check 133-143, nonNegative 159-161, toPositiveLongAtMost 169-172, scheduleNextElection 195-241): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; ElectionStrategy.isElectionQuorum (lines 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L68-L88; the messages PreVoteRequest.java and PreVoteResponse.java in the same directory; CoordinationState (handleStartJoin, handleJoin) as transcribed by the OpenSearchCoordination mission

import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.no_disruption {V : Type} (es : ElectionStrategy) (healthy : DiscoveryNode → Bool)
    (st : DiscoveryNode → CollectorState) (c : DiscoveryNode) (t : Nat) (s : ClusterState V) (L : List NodeId)
    (hL : s.lastCommittedConfiguration.hasQuorum L = true ∨ s.lastAcceptedConfiguration.hasQuorum L = true)
    (hfollow : ∀ n : DiscoveryNode, n.id ∈ L → healthy n = false ∨ ∃ l, (st n).leader = some l ∧ l ≠ c)
    (r : PreVotingRound V)
    (hr : RoundReachable es (fun n resp => handlePreVoteRequest (healthy n) (st n) ⟨c, t⟩ = .ok resp) r)
    (hs : r.clusterState = s) :
    r.electionStarted = false ∧
    ∀ lr resp sender, handlePreVoteRequest (healthy sender) (st sender) ⟨c, t⟩ = .ok resp →
      (r.handlePreVoteResponse es lr resp sender).2.1 = false := by sorry
