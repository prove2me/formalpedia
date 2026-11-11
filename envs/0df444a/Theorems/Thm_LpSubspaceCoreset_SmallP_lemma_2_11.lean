-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_lemma_2_11
-- name    : LpSubspaceCoreset.SmallP.lemma_2_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:47:49.909056+00:00
-- url     : https://prove2.me/theorems/0c0553f4-6d37-4f1e-a516-7d4bd6ad0cab
-- title:
--   Lemma 2.11 — Lewis normalization
-- statement:
--   Let $M\in\mathbb R^{N\times r}$ have full column rank, let $1\le p\le2$, and let $m_i^\top$ and $w_i$ be its rows and ℓp Lewis weights; by the §2.3 convention $M$ has no zero rows. Then there exist an invertible $J\in\mathbb R^{r\times r}$ and unit vectors $y_i\in\mathbb R^r$ with
--   $$m_i=w_i^{1/p}Jy_i,\qquad\sum_iw_iy_iy_i^\top=I_r,\qquad\sum_iw_i=r.\qquad(2.5)$$
--   It is the normal form behind the sensitivity bound of Lemma 2.12.
--
--   Differences from the source:
--   - encoding: zero rows are deleted before computing Lewis weights (§2.3 convention) → hypothesis that M has no zero rows; reason: the lemma is about the matrix after the §2.3 deletion (its proof says so); unit vectors y_i cannot exist for the zero rows of M with r = 0
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), p. 11, Lemma 2.11

import Mathlib
import Definitions.Def_LpSubspaceCoreset_SmallP_Lewis

namespace LpSubspaceCoreset.SmallP

/-- **Lemma 2.11** (Lewis normalization), p. 11.

Let `M ∈ ℝ^{N×r}` have full column rank, let `1 ≤ p ≤ 2`, and let `m_i^⊤` and `w_i` be its rows
and Lewis weights; by the §2.3 convention (zero rows are deleted before computing Lewis weights) `M`
has no zero rows. There exist an invertible `J ∈ ℝ^{r×r}` and unit vectors `y_i ∈ ℝ^r` with
`m_i = w_i^{1/p} J y_i`, `Σ_i w_i y_i y_i^⊤ = I_r` and `Σ_i w_i = r`. -/
theorem lemma_2_11 (p : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) {N r : ℕ}
    (M : Matrix (Fin N) (Fin r) ℝ) (hM : M.rank = r) (hM0 : ∀ i, M i ≠ 0) (w : Fin N → ℝ)
    (hw : IsLewisWeights p M w) :
    ∃ (J : Matrix (Fin r) (Fin r) ℝ) (y : Fin N → Fin r → ℝ), IsUnit J.det ∧
      (∀ i, y i ⬝ᵥ y i = 1) ∧
      (∀ i, M i = (w i) ^ (1 / p) • J.mulVec (y i)) ∧
      ∑ i, w i • Matrix.vecMulVec (y i) (y i) = 1 ∧
      ∑ i, w i = r := by sorry

end LpSubspaceCoreset.SmallP
