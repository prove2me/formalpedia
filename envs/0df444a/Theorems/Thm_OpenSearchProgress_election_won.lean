-- Prove2me | Theorems.Thm_OpenSearchProgress_election_won
-- name    : OpenSearchProgress.election_won
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T01:00:49.48065+00:00
-- url     : https://prove2.me/theorems/a6cabeb7-5937-4b96-b037-af6ddc72fa73
-- title:
--   A stable election is won once the votes of a quorum are counted
-- statement:
--   For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, every node `c`, term `t` and list of node ids `Q` such that
--
--   - `c` and every member of `Q` are cluster-manager-eligible;
--   - `Q` is a quorum of both of `c`'s configurations: `(W.node c).lastCommittedConfiguration.hasQuorum Q = true` and `(W.node c).lastAcceptedConfiguration.hasQuorum Q = true`;
--   - `c` and every member of `Q` are in a term below `t`: `(W.node q).currentTerm < t` for `q = c` and for every `q ∈ Q`;
--
--   and every cluster `W'` with `ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W'` such that `(W'.node c).currentTerm = t` and every member of `Q` is among `c`'s join votes (`q ∈ (W'.node c).joinVotes.nodes` for every `q ∈ Q`): `(W'.node c).electionWon = true`.
--
--   No hypothesis on the voters' accepted states is needed: the votes are already counted. During the period `c`'s committed configuration may change by a commit, but only to its accepted configuration, of which `Q` is also a quorum.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: Coordinator (handlePublishRequest lines 454-526 with ensureTermAtLeast at 512, startElection 583-602, ensureTermAtLeast 635-641, joinLeaderInTerm 643-657, handleJoin 1267-1287 with handleJoinIgnoringExceptions 1289-1299, publish 1350 with the handleClientValue call at 1404, CoordinatorPublication.handlePublishResponse 1871-1875): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; CoordinationState (isPublishQuorum lines 156-158, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573) as transcribed by the OpenSearchCoordination mission: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java; the cluster model, the safety vocabulary and the inductive invariant of the OpenSearchSafety mission (Step, Reachable, Committed, Inv, reachable_inv); for why progress needs a stable period: M. J. Fischer, N. A. Lynch, M. S. Paterson, Impossibility of distributed consensus with one faulty process, J. ACM 32(2), 1985, and C. Dwork, N. Lynch, L. Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35(2), 1988

import Definitions.Def_OpenSearchProgress
open OpenSearchCoordination OpenSearchSafety OpenSearchProgress

theorem OpenSearchProgress.election_won {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hc : P.eligible c = true) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hquorum : (W.node c).lastCommittedConfiguration.hasQuorum Q = true ∧
      (W.node c).lastAcceptedConfiguration.hasQuorum Q = true)
    (hterm : ∀ q, q = c ∨ q ∈ Q → (W.node q).currentTerm < t)
    (W' : Cluster V)
    (hE : ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W')
    (hct : (W'.node c).currentTerm = t) (hvotes : ∀ q ∈ Q, q ∈ (W'.node c).joinVotes.nodes) :
    (W'.node c).electionWon = true := by sorry
