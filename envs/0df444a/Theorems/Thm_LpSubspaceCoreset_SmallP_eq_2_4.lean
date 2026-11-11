-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_eq_2_4
-- name    : LpSubspaceCoreset.SmallP.eq_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:47:54.694308+00:00
-- url     : https://prove2.me/theorems/e77833db-5c3a-4af5-874c-92140213d26d
-- title:
--   §2.3, Eq. (2.4) — ℓp Lewis weights exist, are unique for 1 ≤ p < 4, and sum to rank(M)
-- statement:
--   Let $1\le p<4$ and let $M\in\mathbb R^{N\times r}$ have full column rank ($\operatorname{rank}M=r$). Then the ℓp Lewis weights of $M$ (Definition 2.8, zero rows restored with weight $0$) exist, they are unique, and
--   $$\sum_{i=1}^N w_i=\operatorname{rank}(M)=r.\qquad(2.4)$$
--   The paper quotes existence and uniqueness from Cohen and Peng [CP15, Sec. 3, Cor. 3.4]; it makes the Lewis-weight hypotheses of the later statements non-vacuous.
--
--   Differences from the source: none.
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), p. 11, §2.3, Eq. (2.4)

import Mathlib
import Definitions.Def_LpSubspaceCoreset_SmallP_Lewis

namespace LpSubspaceCoreset.SmallP

/-- **§2.3, Eq. (2.4)** (Cohen–Peng existence and uniqueness), p. 11.

Let `1 ≤ p < 4` and let `M ∈ ℝ^{N×r}` have full column rank (`rank M = r`). Then the ℓp Lewis
weights of `M` (Definition 2.8, zero rows restored with weight `0`) exist, are unique, and sum to
`rank(M) = r`. -/
theorem eq_2_4 (p : ℝ) (hp : 1 ≤ p) (hp4 : p < 4) {N r : ℕ} (M : Matrix (Fin N) (Fin r) ℝ)
    (hM : M.rank = r) :
    (∃ w : Fin N → ℝ, IsLewisWeights p M w) ∧
    (∀ w w' : Fin N → ℝ, IsLewisWeights p M w → IsLewisWeights p M w' → w = w') ∧
    (∀ w : Fin N → ℝ, IsLewisWeights p M w → ∑ i, w i = r) := by sorry

end LpSubspaceCoreset.SmallP
