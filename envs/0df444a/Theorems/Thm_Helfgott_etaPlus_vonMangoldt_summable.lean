-- Prove2me | Theorems.Thm_Helfgott_etaPlus_vonMangoldt_summable
-- name    : Helfgott.etaPlus_vonMangoldt_summable
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T22:29:04.24349+00:00
-- url     : https://prove2.me/theorems/f8198f46-074c-4b87-a920-852f9d1bf1a0
-- title:
--   Absolute convergence of the actual band-limited Gaussian von Mangoldt sum
-- statement:
--   For every real x>0, the actual final Helfgott smoothing η+(t)=h₂₀₀(t)t exp(−t²/2) gives an absolutely convergent sum ∑ₙΛ(n)η+(n/x). Here h₂₀₀ is the published Mellin convolution with the sinc band kernel. The estimate allows signed η+ weights and retains the infinite tails. This is the convergence input to the circle-method counting identity, independent of the sharper numerical sup-norm bound.
-- source:
--   Derived convergence result for the exact smoothing in Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, final section-7 definitions; Major arcs for Goldbach’s problem, arXiv:1305.2897v3, equations (1.4)–(1.5) and Appendix B. https://arxiv.org/pdf/1305.2897v3 . Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Definitions.Def_Helfgott_PrimePowerRemoval
open MeasureTheory
open scoped BigOperators

namespace Helfgott

theorem etaPlus_vonMangoldt_summable (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * etaPlus ((n : ℝ)/x)) := by sorry

end Helfgott
