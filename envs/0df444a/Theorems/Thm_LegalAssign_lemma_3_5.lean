-- Prove2me | Theorems.Thm_LegalAssign_lemma_3_5
-- name    : LegalAssign.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:23:00.52298+00:00
-- url     : https://prove2.me/theorems/c20914c6-dc49-40d0-b1da-93a18258170e
-- title:
--   Lemma 3.5 — $\mathcal L$ is the legal set of $G_L$
-- statement:
--   Let $\mathcal L$ be the legal set of $(G,<,q)$ and let $G_L:=G[\bigcup\{M:M\in\mathcal L\}]$. Then
--   $$\mathcal L=\mathcal L(G_L,<,q).$$
--
--   This is the effect of deleting all illegal edges.
--
--   Differences from the source:
--   - encoding: <_v is a strict ordering of the neighbours of v in G → prefA a and prefB b are strict total orders on the whole other side; reason: only comparisons among neighbours ever enter, and every strict order on the neighbours extends to the whole side
--   - encoding: G is a bipartite graph, finite throughout the paper → Fintype A, Fintype B, E : Finset (A × B), assignments are Finsets of pairs; reason: Lean convention; the same instances
--   - reading: q = {q_b} ∈ ℕ^B, with no statement on whether this ℕ contains 0 → q : B → ℕ, so q_b = 0 is allowed; reason: the source does not settle it, and the Lean statement covers positive quotas and quota 0 alike
--   - encoding: 𝓛 is the legal set 𝓛(G, <, q) and 𝓛(·) denotes the unique legal set, defined through Theorem 3.3 → L is a bound set with L ⊆ 𝓜 and the legal property; 𝓛(H) = X is the equivalence (S ⊆ 𝓜(H) ∧ S is legal in H) ↔ S = X; reason: equivalent to the equality and needs no choice function
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, Lemma 3.5, p.8

import Mathlib
import Definitions.Def_LegalAssign_Instance

namespace LegalAssign

/-- Lemma 3.5 (arXiv:1809.08506v2, p.8): if `𝓛` is the legal set of `G`, it is the legal set of
`G_L := G[⋃{M : M ∈ 𝓛}]`.

**Formalization Note** As in Lemma 3.4, the unique legal set is expressed without a choice function. -/
theorem lemma_3_5 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) (L : Set (Finset (A × B)))
    (hL : L ⊆ G.assignments) (hlegal : G.HasLegalProperty L) (S : Set (Finset (A × B))) :
    (S ⊆ (G.restrict (edgeUnion L)).assignments ∧
        (G.restrict (edgeUnion L)).HasLegalProperty S) ↔ S = L := by sorry

end LegalAssign
