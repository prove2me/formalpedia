-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_lemma_2_12
-- name    : LpSubspaceCoreset.SmallP.lemma_2_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:47:55.910692+00:00
-- url     : https://prove2.me/theorems/b91c1962-ed74-4a02-9e4a-d2b1d0ec9e61
-- title:
--   Lemma 2.12 — Lewis weights bound (p, 2)-sensitivities
-- statement:
--   Let $M\in\mathbb R^{N\times r}$ have full column rank, let $1\le p\le2$, and let $m_i^\top$ and $w_i$ be its rows and ℓp Lewis weights. For every $s\ge1$, every matrix $T\in\mathbb R^{s\times r}$ and every row $i$,
--   $$\|Tm_i\|_2^p\le w_i\sum_j\|Tm_j\|_2^p.\qquad(2.6)$$
--   It bounds the share of the low-rank part of the cost that a single row can carry, uniformly over all linear maps.
--
--   Differences from the source: none.
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), p. 12, Lemma 2.12

import Mathlib
import Definitions.Def_LpSubspaceCoreset_SmallP_Cost
import Definitions.Def_LpSubspaceCoreset_SmallP_Lewis

namespace LpSubspaceCoreset.SmallP

/-- **Lemma 2.12** (Lewis weights bound `(p, 2)`-sensitivities), p. 12.

Let `M ∈ ℝ^{N×r}` have full column rank, let `1 ≤ p ≤ 2`, and let `m_i^⊤` and `w_i` be its rows
and Lewis weights. For every `s ≥ 1`, every `T ∈ ℝ^{s×r}` and every row `i`,
`‖T m_i‖₂^p ≤ w_i Σ_j ‖T m_j‖₂^p`. -/
theorem lemma_2_12 (p : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) {N r : ℕ}
    (M : Matrix (Fin N) (Fin r) ℝ) (hM : M.rank = r) (w : Fin N → ℝ)
    (hw : IsLewisWeights p M w) (s : ℕ) (hs : 1 ≤ s) (T : Matrix (Fin s) (Fin r) ℝ)
    (i : Fin N) :
    norm2 (T.mulVec (M i)) ^ p ≤ w i * ∑ j, norm2 (T.mulVec (M j)) ^ p := by sorry

end LpSubspaceCoreset.SmallP
