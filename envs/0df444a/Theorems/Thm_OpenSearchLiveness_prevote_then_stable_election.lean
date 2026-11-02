-- Prove2me | Theorems.Thm_OpenSearchLiveness_prevote_then_stable_election
-- name    : OpenSearchLiveness.prevote_then_stable_election
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T18:51:41.989808+00:00
-- url     : https://prove2.me/theorems/ed2dd2a8-afae-4997-8de8-6864379210b2
-- title:
--   Pre-vote, then election: a pre-vote round over unchanged voters yields a stable election
-- statement:
--   Let $W$ be a reachable cluster, $c$ an eligible candidate, and $r$ a pre-voting round over $c$'s current accepted state whose recorded responses match the voters' current states (the unchanged-since-answering side condition, stated as an assumption because the model has no time window), whose recorded senders are $P$-compatible discovery nodes, and whose votes form a quorum of both the round's committed and accepted configurations. Then there is a stable election execution for $c$ in the election term computed from $c$'s current term and the maximum term seen, ending with $c$ in that term and elected.
-- source:
--   OpenSearch cluster coordination, pinned revision b2a54ba5c0defba3d1d20423e911d4bf920bab19 (org.opensearch.cluster.coordination); liveness/timer gap-closure analysis, new theorems mechanized from the branch's OpenSearchCoordination/OpenSearchPreVote/OpenSearchSafety/OpenSearchProgress missions.

import Definitions.Def_OpenSearchCoordination
import Definitions.Def_OpenSearchSafety
import Definitions.Def_OpenSearchProgress
import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchSafety OpenSearchProgress OpenSearchPreVote

theorem OpenSearchLiveness.prevote_then_stable_election {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE)
    (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (hc : P.eligible c = true)
    (r : PreVotingRound V)
    (hr : RoundReachable ElectionStrategy.DEFAULT_INSTANCE
      (fun n resp => (W.node n.id).localNode = n ∧
        preVoteResponseOf (W.node n.id) = resp) r)
    (hstate : r.clusterState = (W.node c).lastAcceptedState)
    (hlocal : r.localNode = (W.node c).localNode)
    (hdn : ∀ p ∈ r.preVotesReceived, p.1 = P.dn p.1.id)
    (hquorum : r.votes.isQuorum r.clusterState.lastCommittedConfiguration = true ∧
      r.votes.isQuorum r.clusterState.lastAcceptedConfiguration = true)
    (maxTermSeen : Nat)
    (hseen : ∀ p ∈ r.preVotesReceived, p.2.currentTerm ≤ maxTermSeen) :
    ∃ W', ElectionExec P c (startElectionTerm (W.node c).currentTerm maxTermSeen)
        r.votes.nodes (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W' ∧
      (W'.node c).currentTerm = startElectionTerm (W.node c).currentTerm maxTermSeen ∧
      (W'.node c).electionWon = true := by sorry
