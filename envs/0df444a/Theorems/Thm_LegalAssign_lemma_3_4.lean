-- Prove2me | Theorems.Thm_LegalAssign_lemma_3_4
-- name    : LegalAssign.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:38.257282+00:00
-- url     : https://prove2.me/theorems/3eb3e26e-6d24-42f9-a3b1-74db481d919d
-- title:
--   Lemma 3.4 — deleting an illegal edge keeps the legal set
-- statement:
--   Let $\mathcal L$ be the legal set of $(G,<,q)$, let $e\in E$ be **illegal**, meaning that $e$ lies in no assignment of $\mathcal L$, and let $\tilde G:=G[E\setminus\{e\}]$. Then
--   $$\mathcal L=\mathcal L(\tilde G,<,q).$$
--
--   Illegal edges can therefore be removed without changing the set of legal assignments.
--
--   Differences from the source:
--   - encoding: <_v is a strict ordering of the neighbours of v in G → prefA a and prefB b are strict total orders on the whole other side; reason: only comparisons among neighbours ever enter, and every strict order on the neighbours extends to the whole side
--   - encoding: G is a bipartite graph, finite throughout the paper → Fintype A, Fintype B, E : Finset (A × B), assignments are Finsets of pairs; reason: Lean convention; the same instances
--   - reading: q = {q_b} ∈ ℕ^B, with no statement on whether this ℕ contains 0 → q : B → ℕ, so q_b = 0 is allowed; reason: the source does not settle it, and the Lean statement covers positive quotas and quota 0 alike
--   - encoding: 𝓛 is the legal set 𝓛(G, <, q) and 𝓛(·) denotes the unique legal set, defined through Theorem 3.3 → L is a bound set with L ⊆ 𝓜 and the legal property; 𝓛(H) = X is the equivalence (S ⊆ 𝓜(H) ∧ S is legal in H) ↔ S = X; reason: equivalent to the equality and needs no choice function
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, Lemma 3.4, p.8

import Mathlib
import Definitions.Def_LegalAssign_Instance

namespace LegalAssign

/-- Lemma 3.4 (arXiv:1809.08506v2, p.8): if `𝓛` is the legal set of `G` and `e` is an illegal edge, then
`𝓛` is the legal set of `G̃ := G[E \ {e}]`.

**Formalization Note** The source's `𝓛(G̃, <, q)` is defined through Theorem 3.3. The statement avoids
a choice function: the sets with the legal property in `G̃` are exactly `𝓛`. -/
theorem lemma_3_4 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) (L : Set (Finset (A × B)))
    (hL : L ⊆ G.assignments) (hlegal : G.HasLegalProperty L)
    (e : A × B) (he : e ∈ G.E) (hille : e ∉ edgeUnion L) (S : Set (Finset (A × B))) :
    (S ⊆ (G.restrict (G.E.erase e)).assignments ∧
        (G.restrict (G.E.erase e)).HasLegalProperty S) ↔ S = L := by sorry

end LegalAssign
