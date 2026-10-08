-- Prove2me | Theorems.Thm_Helfgott_weighted_ternary_counting
-- name    : Helfgott.weighted_ternary_counting
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T20:57:39.714815+00:00
-- url     : https://prove2.me/theorems/c9288b9d-a7c8-4611-ac87-f834c1a58e59
-- title:
--   Absolutely convergent weighted ternary circle-method identity
-- statement:
--   Let $a,b,c$ be absolutely summable complex sequences indexed by the nonnegative integers. Then, for every nonnegative integer $N$,
--
--   $$\int_{\mathbb R/\mathbb Z} S_a(\alpha)S_b(\alpha)S_c(\alpha)e(-N\alpha)\,d\alpha
--    =\sum_{i+j+k=N}a_i b_j c_k.$$
--
--   The circle carries probability Haar measure. The three exponential sums are infinite, so the theorem applies to noncompact Gaussian-based smoothing coefficients after their summability is established. Specializing $a=b$ and $a_n=\Lambda(n)\eta_+(n/x)$, $c_n=\Lambda(n)\eta_*(n/x)$ gives the identity used in Helfgott’s final major/minor-arc argument. This theorem establishes the counting identity, without any estimate for the arc integrals or any assertion of Goldbach itself.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equations (1.3) and (7.49), §1.3 and §7.4 (printed pp. 69–71 for the conclusion). https://arxiv.org/abs/1312.7748 . General coefficient interface for the weighted sums, with a_n=Λ(n)η(n/x) in the paper. Written by Codex.

import Definitions.Def_Helfgott_WeightedCounting
open MeasureTheory
open scoped BigOperators

namespace Helfgott

theorem weighted_ternary_counting (a b c : ℕ → ℂ) (ha : Summable a)
    (hb : Summable b) (hc : Summable c) (N : ℕ) :
    (∫ α : AddCircle (1 : ℝ),
      expSum a α * expSum b α * expSum c α * fourier (-(N : ℤ)) α
        ∂AddCircle.haarAddCircle) = tripleCount a b c N := by sorry

end Helfgott
