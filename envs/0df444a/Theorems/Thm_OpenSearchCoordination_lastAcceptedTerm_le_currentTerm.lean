-- Prove2me | Theorems.Thm_OpenSearchCoordination_lastAcceptedTerm_le_currentTerm
-- name    : OpenSearchCoordination.lastAcceptedTerm_le_currentTerm
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:33:03.955189+00:00
-- url     : https://prove2.me/theorems/e109b73a-2221-470c-a031-0736abd6ff9f
-- title:
--   Only handleStartJoin changes the current term, and every handler keeps the accepted term at most the current term
-- statement:
--   For every election strategy `es` and coordination state `cs` with `cs.lastAcceptedTerm ≤ cs.currentTerm`, every successful handler call on `cs` — for `setInitialState s`, one with `s.term = 0`, one of the method's asserted preconditions (a conjunct of `initialStateContract`, the only one assumed) — yields a state `cs'` with `cs'.lastAcceptedTerm ≤ cs'.currentTerm`, and moreover:
--
--   - `cs.setInitialState s = .ok cs'` with `s.term = 0` leaves the current term unchanged;
--   - `cs.handleStartJoin r = .ok (cs', j)` strictly increases it: `cs.currentTerm < cs'.currentTerm`;
--   - `cs.handleJoin es j`, `cs.handleClientValue s`, `cs.handlePublishRequest p`, `cs.handlePublishResponse n r` and `cs.handleCommit c`, when they succeed, leave it unchanged.
--
--   So the first assertion of `invariant()`, `getLastAcceptedTerm() <= getCurrentTerm()`, is preserved by one successful call of any handler, and along successful calls on one node that start from a state satisfying it (with term-0 states for `setInitialState`) the current term changes only at `handleStartJoin`, upwards. The statement is about single steps; it does not mention `init`, whose result satisfies the inequality exactly when `s.term ≤ t` (the hypothesis of `init_javaInvariant`).
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (constructor lines 84-106, isElectionQuorum 144-154, isPublishQuorum 156-158, setInitialState 180-204, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573, invariant 601-611, PersistedState.markLastAcceptedStateAsCommitted 703-728, commitVotingConfiguration 730-740, VoteCollection 750-814), server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java: https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java#L64-L815; CoordinationMetadata.VotingConfiguration (lines 383-449, hasQuorum 405-409): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationMetadata.java#L383-L449; ElectionStrategy (DEFAULT_INSTANCE lines 46-59, isElectionQuorum 68-88): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; ClusterState.getVersionOrMetadataVersion (lines 239-244): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/ClusterState.java#L239-L244; Coordinator.ZEN1_BWC_TERM (line 134): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L134; the messages StartJoinRequest.java, Join.java, PublishRequest.java, PublishResponse.java, ApplyCommitRequest.java in the same directory; test vectors from server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java (https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java) and CoordinationMetadataTests.java (testVotingConfiguration)

import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.lastAcceptedTerm_le_currentTerm {V : Type} (es : ElectionStrategy) (cs : CoordinationState V)
    (hcs : cs.lastAcceptedTerm ≤ cs.currentTerm) :
    (∀ s cs', cs.setInitialState s = .ok cs' → s.term = 0 → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ r cs' j, cs.handleStartJoin r = .ok (cs', j) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs.currentTerm < cs'.currentTerm) ∧
    (∀ j cs' b, cs.handleJoin es j = .ok (cs', b) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ s cs' p, cs.handleClientValue s = .ok (cs', p) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ p cs' r, cs.handlePublishRequest p = .ok (cs', r) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ n r cs' o, cs.handlePublishResponse n r = .ok (cs', o) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ c cs', cs.handleCommit c = .ok cs' → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) := by sorry
