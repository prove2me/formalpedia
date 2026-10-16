-- Prove2me | Theorems.Thm_JRPHard_Shor_subset_sum_iff_product
-- name    : JRPHard.Shor.subset_sum_iff_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:39:40.300128+00:00
-- url     : https://prove2.me/theorems/74722b5a-4476-473e-909f-541af33ae4a2
-- title:
--   Appendix, p. 17 — subset sums and products
-- statement:
--   Let $n\ge1$, $B\ge1$, and $2^B\le a_i<2^{B+1}$ for every index. Suppose the total $\sum_i a_i$ is even, and each natural number $p_i$ satisfies the final multiplicative window
--   $$2^{b_i}2^{-\lambda/(2n)}<p_i<2^{b_i}2^{\lambda/(2n)}.$$
--   For every index subset $S$,
--   $$2\sum_{i\in S}a_i=\sum_i a_i\quad\Longleftrightarrow\quad L<\prod_{i\in S}p_i<U.$$
--   Thus the exact half-sum subsets are precisely the subproducts in the open interval. Evenness is necessary for the converse: with an odd total, a half-integral $A$ allows a nearby integer subtotal to fall inside the interval.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 17, Appendix, first sentence

import Mathlib
import Definitions.Def_JRPHard_Shor_Setting

namespace JRPHard.Shor

open Finset

/-- Appendix, p. 17: a half-sum subset is exactly a product in the open interval. -/
theorem subset_sum_iff_product (n B : ℕ) (hn : 0 < n) (hB : 1 ≤ B)
    (a : Fin n → ℕ) (ha : ∀ i, 2 ^ B ≤ a i ∧ a i < 2 ^ (B + 1))
    (heven : Even (∑ i, a i)) (p : Fin n → ℕ)
    (hwindow : ∀ i, (2 : ℝ) ^ (expo B a i) *
          (2 : ℝ) ^ (-(scale B / (2 * (n : ℝ)))) < (p i : ℝ) ∧
        (p i : ℝ) < (2 : ℝ) ^ (expo B a i) *
          (2 : ℝ) ^ (scale B / (2 * (n : ℝ))))
    (S : Finset (Fin n)) :
    (2 * ∑ i ∈ S, a i = ∑ i, a i) ↔
      (lowL B a < ∏ i ∈ S, (p i : ℝ)) ∧
      (∏ i ∈ S, (p i : ℝ)) < highU B a := by sorry

end JRPHard.Shor
