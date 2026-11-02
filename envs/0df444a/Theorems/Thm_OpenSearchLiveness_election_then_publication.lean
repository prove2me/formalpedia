-- Prove2me | Theorems.Thm_OpenSearchLiveness_election_then_publication
-- name    : OpenSearchLiveness.election_then_publication
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T18:51:41.240077+00:00
-- url     : https://prove2.me/theorems/60d10e6b-0950-4bae-96d6-0e084f2a5702
-- title:
--   Election, then publication: a win plus a successful client value starts a stable publication
-- statement:
--   Let $W$ be a reachable cluster in which $c$ has won the election in term $t$, and let a client value $s$ of term $t$ be accepted by $c$'s $\mathrm{handleClientValue}$ under its guards and its contract that the committed configuration does not change, with the record-update facts of the success branch stated explicitly as hypotheses. Then there is a stable publication execution starting from the publication of $s$ that ends with version $s.\mathrm{version}$ committed in term $t$.
-- source:
--   OpenSearch cluster coordination, pinned revision b2a54ba5c0defba3d1d20423e911d4bf920bab19 (org.opensearch.cluster.coordination); liveness/timer gap-closure analysis, new theorems mechanized from the branch's OpenSearchCoordination/OpenSearchPreVote/OpenSearchSafety/OpenSearchProgress missions.

import Definitions.Def_OpenSearchCoordination
import Definitions.Def_OpenSearchSafety
import Definitions.Def_OpenSearchProgress
import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchSafety OpenSearchProgress OpenSearchPreVote

theorem OpenSearchLiveness.election_then_publication {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE)
    (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId)
    (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hwon : (W.node c).electionWon = true) (hct : (W.node c).currentTerm = t)
    (s : ClusterState V) (cs' : CoordinationState V) (p : PublishRequest V)
    (hcv : (W.node c).handleClientValue s = .ok (cs', p))
    (hcontract : (W.node c).clientValueContract s)
    (hfields : cs'.electionWon = (W.node c).electionWon ∧
      cs'.currentTerm = (W.node c).currentTerm ∧
      cs'.lastCommittedConfiguration = (W.node c).lastCommittedConfiguration ∧
      cs'.lastAcceptedConfiguration = (W.node c).lastAcceptedConfiguration ∧
      cs'.lastPublishedVersion = s.version ∧ cs'.publishVotes.nodes = [])
    (hpacc : p.acceptedState = s)
    (hst : s.term = t)
    (hquorum : (W.node c).lastCommittedConfiguration.hasQuorum Q = true ∧
      (W.node c).lastAcceptedConfiguration.hasQuorum Q = true ∧
      s.lastCommittedConfiguration.hasQuorum Q = true ∧
      s.lastAcceptedConfiguration.hasQuorum Q = true)
    (hterm : ∀ q ∈ Q, (W.node q).currentTerm ≤ t) :
    ∃ W', PublicationExec P c t Q
        ((W.set c cs').send (.publishRequest c p.acceptedState
          (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion)) W' ∧
      Committed W' t p.acceptedState.version := by sorry
