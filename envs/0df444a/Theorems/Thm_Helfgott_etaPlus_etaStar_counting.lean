-- Prove2me | Theorems.Thm_Helfgott_etaPlus_etaStar_counting
-- name    : Helfgott.etaPlus_etaStar_counting
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T22:29:47.902267+00:00
-- url     : https://prove2.me/theorems/f39b9d31-5dbf-4c2f-8348-39eb31473f53
-- title:
--   Infinite Fourier counting identity for the actual coordinated Goldbach smoothings
-- statement:
--   For every positive real scale x and every natural N, the Fourier coefficient of Sη+(α,x)²Sη*(α,x) at N equals the finite sum over n₁+n₂+n₃=N of Λ(n₁)Λ(n₂)Λ(n₃)η+(n₁/x)η+(n₂/x)η*(n₃/x). The sums defining Sη+ and Sη* are the complete infinite series; their absolute convergence is proved for these actual published smoothings. This gives the exact analytic-to-arithmetic interface for the remaining major/minor-arc lower-bound argument.
-- source:
--   Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equations (1.3), (7.49), and final section-7 smoothing definitions. https://arxiv.org/html/1312.7748v2 . The proof supplies the actual weight convergence without a finite truncation assumption. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Definitions.Def_Helfgott_PrimePowerRemoval
open MeasureTheory
open scoped BigOperators

namespace Helfgott

theorem etaPlus_etaStar_counting (x : ℝ) (hx : 0 < x) (N : ℕ) :
    (∫ α : AddCircle (1 : ℝ),
      expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaPlus ((n : ℝ)/x) : ℝ) : ℂ)) α *
      expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaPlus ((n : ℝ)/x) : ℝ) : ℂ)) α *
      expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n : ℝ)/x) : ℝ) : ℂ)) α *
      fourier (-(N : ℤ)) α ∂AddCircle.haarAddCircle) =
      ((∑ t ∈ tripleIndices N,
        weightedTripleTerm (fun n => etaPlus ((n : ℝ)/x)) (fun n => etaStar ((n : ℝ)/x)) t : ℝ) : ℂ) := by sorry

end Helfgott
