-- Prove2me | Theorems.Thm_MISInducedMinor_lemma_3_2
-- name    : MISInducedMinor.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:02.195821+00:00
-- url     : https://prove2.me/theorems/8b0d6351-42bf-4195-9df3-141d7a14dace
-- title:
--   Lemma 3.2 — $\alpha(G_F)=\mathrm{MaxCut}(F)+2\sum(j'-j)$
-- statement:
--   **Lemma 3.2.** For every graph $F$ with ordered vertices $v_1,\dots,v_n$,
--
--   $$\alpha(G_F)=\mathrm{MaxCut}(F)+2\sum_{\substack{v_jv_{j'}\in E(F)\\ j<j'}}(j'-j).$$
--
--   Since the additive term is computable in polynomial time, deciding $\alpha(G_F)\ge k'$ decides $\mathrm{MaxCut}(F)\ge k'-2\sum(j'-j)$. This is the half of Theorem 1.5 that transfers the hardness of Max Cut.
--
--   **Formalization Note** $\alpha$ is Mathlib's `indepNum`. The statement covers $n=0$ and edgeless $F$, where both sides are $0$.
--
--   Differences from the source:
--   - encoding: indices are 1-based: rows [2m], columns [2n − 1], vertex v_j in column 2j − 1 → 0-based: rows Fin (2m), columns Fin (2n − 1), vertex j − 1 : Fin n in column 2(j − 1); reason: Lean convention; the same graph up to the shift of indices, and Σ(j′ − j) is shift-invariant
--   - encoding: the vertices of F are ordered arbitrarily as v_1, …, v_n, and each edge e gets two reserved rows e_0, e_1 → F is a graph on Fin n with the order of Fin n, and edge number t of the lexicographic list of pairs a < b gets rows 2t (side 0) and 2t + 1 (side 1); reason: any vertex order is the order of Fin n after relabelling F, and the statement holds for every F; permuting rows is an automorphism of G, so the row assignment changes G_F only up to isomorphism
--   - encoding: MaxCut(F), the number of edges in a maximum-cardinality cut → the maximum over all A ⊆ V(F) of the number of pairs (a, b) ∈ A × Aᶜ with ab ∈ E(F); reason: each cut edge is exactly one such pair; the maximum is over a finite set, so it is attained
--   - encoding: ∑_{v_jv_j′ ∈ E(F), j<j′} (j′ − j) → the sum of b − a over the entries (a, b) of the canonical edge list, which have a < b; reason: natural-number subtraction is exact since a < b; the same number
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), Lemma 3.2, p.7

import Definitions.Def_MISInducedMinor_GF
import Definitions.Def_MISInducedMinor_maxCut
import Definitions.Def_MISInducedMinor_addTerm

set_option autoImplicit false

namespace MISInducedMinor

/-- **Lemma 3.2.** `α(G_F) = MaxCut(F) + 2 ∑_{vⱼvⱼ′ ∈ E(F), j < j′} (j′ − j)`.
arXiv:2609.11285 (sha256 e378b906…), Lemma 3.2, p.7.

**Formalization Note.** `α` is Mathlib's `indepNum`; for every `n` and every `F`, including
`n = 0` and edgeless `F`, where both sides are `0`. -/
theorem lemma_3_2 (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    (GF F).indepNum = maxCut F + 2 * addTerm F := by sorry

end MISInducedMinor
