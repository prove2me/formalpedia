-- Prove2me | Theorems.Thm_OpenSearchPreVote_preVote_then_election
-- name    : OpenSearchPreVote.preVote_then_election
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:36:18.457022+00:00
-- url     : https://prove2.me/theorems/3080d3dc-5072-4761-a37a-13a0025812b1
-- title:
--   A successful pre-vote predicts a successful election
-- statement:
--   Let `csc` be the coordination state of a node `c`, and `node n` the coordination state in which each node `n` handles `c`'s start-join request. Let `r` be a round reachable under the default election strategy in which a response `resp` can be delivered from `n` only if `(node n).localNode = n` and `preVoteResponseOf (node n) = resp`: the senders' current term and accepted term and version have not changed since they answered. Suppose `r.clusterState = csc.lastAcceptedState`, `r.localNode = csc.localNode`, and `r.electionStarted = true`. Let `maxTermSeen` be at least the current term of every recorded response (`updateMaxTermSeen` makes it so) and `T = startElectionTerm csc.currentTerm maxTermSeen`, that is `max(csc.currentTerm, maxTermSeen) + 1`. Let `csc.handleStartJoin ⟨csc.localNode, T⟩ = .ok (csc₁, j₀)`, and let `js` be any list of joins whose terms are all at most `T`. Then:
--
--   1. every recorded sender `p.1` accepts the request: `(node p.1).handleStartJoin ⟨csc.localNode, T⟩` succeeds;
--   2. if every join the recorded senders produce from that request occurs in `js`, then `(handleJoins ElectionStrategy.DEFAULT_INSTANCE csc₁ js).electionWon = true`.
--
--   The senders' joins may arrive in any order, interleaved with any other joins of term at most `T`, accepted or rejected (a rejected join leaves the state unchanged), and `c` handles nothing else in between. The bound on the join terms restricts the statement to the joins `Coordinator.handleJoin` handles without first moving `c` to a higher term (CO:1269), which would discard the votes.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: PreVoteCollector (state line 79, start 111-115, update 128-131, handlePreVoteRequest 133-163, PreVotingRound 175-300, handlePreVoteResponse 225-279, close 296-299): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PreVoteCollector.java#L66-L301; Coordinator (updateMaxTermSeen lines 560-581, startElection 583-602, nodeMayWinElection 628-633, getPreVoteResponse 873-879, handleJoin 1267-1299, startElectionScheduler 1567-1618, the preVoteCollector.update calls 516, 653, 777, 801, 839, 1157): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L560-L633; ElectionSchedulerFactory (settings lines 85-115, constructor check 133-143, nonNegative 159-161, toPositiveLongAtMost 169-172, scheduleNextElection 195-241): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; ElectionStrategy.isElectionQuorum (lines 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L68-L88; the messages PreVoteRequest.java and PreVoteResponse.java in the same directory; CoordinationState (handleStartJoin, handleJoin) as transcribed by the OpenSearchCoordination mission

import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.preVote_then_election {V : Type} (csc : CoordinationState V)
    (node : DiscoveryNode → CoordinationState V) (r : PreVotingRound V)
    (hr : RoundReachable ElectionStrategy.DEFAULT_INSTANCE
      (fun n resp => (node n).localNode = n ∧ preVoteResponseOf (node n) = resp) r)
    (hstate : r.clusterState = csc.lastAcceptedState) (hlocal : r.localNode = csc.localNode)
    (hstarted : r.electionStarted = true) (maxTermSeen : Nat)
    (hseen : ∀ p ∈ r.preVotesReceived, p.2.currentTerm ≤ maxTermSeen)
    (csc₁ : CoordinationState V) (j₀ : Join)
    (hsj : csc.handleStartJoin ⟨csc.localNode, startElectionTerm csc.currentTerm maxTermSeen⟩ = .ok (csc₁, j₀))
    (js : List Join) (hjs : ∀ j ∈ js, j.term ≤ startElectionTerm csc.currentTerm maxTermSeen) :
    (∀ p ∈ r.preVotesReceived, ∃ cs' j,
      (node p.1).handleStartJoin ⟨csc.localNode, startElectionTerm csc.currentTerm maxTermSeen⟩ = .ok (cs', j)) ∧
    ((∀ p ∈ r.preVotesReceived, ∀ cs' j,
      (node p.1).handleStartJoin ⟨csc.localNode, startElectionTerm csc.currentTerm maxTermSeen⟩ = .ok (cs', j) →
        j ∈ js) →
      (handleJoins ElectionStrategy.DEFAULT_INSTANCE csc₁ js).electionWon = true) := by sorry
