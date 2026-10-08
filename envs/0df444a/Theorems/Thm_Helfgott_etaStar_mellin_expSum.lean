-- Prove2me | Theorems.Thm_Helfgott_etaStar_mellin_expSum
-- name    : Helfgott.etaStar_mellin_expSum
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T23:08:31.347573+00:00
-- url     : https://prove2.me/theorems/725b9cce-ddf3-43dc-971e-4d4495a06c45
-- title:
--   Exact Mellin transfer of the coordinated Gaussian exponential sum
-- statement:
--   For the actual smoothing η*(t)=(η₂ *_M φ)(49t), every x>0 and every circle frequency α, the complete von Mangoldt exponential sum equals ∫₀∞Sη₂(xw/49,α)φ(w)dw/w. The transfer integrand is absolutely integrable, and its integral gives the corresponding bound on |Sη*(x,α)|. The proof establishes convergence and the interchange of the complete infinite sum with the integral, retaining all Gaussian tails.
-- source:
--   Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equation (4.9), with the final coordinated scaling κ=49. https://arxiv.org/html/1312.7748v2 . Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Definitions.Def_Helfgott_WeightedCounting
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
open MeasureTheory

namespace Helfgott

theorem etaStar_mellin_expSum (x : ℝ) (hx : 0 < x) (α : AddCircle (1 : ℝ)) :
    IntegrableOn (fun w : ℝ =>
      expSum (fun n => ((ArithmeticFunction.vonMangoldt n*
        etaTwo ((n : ℝ)/(x*w/49)) : ℝ) : ℂ)) α * ((phi w/w : ℝ) : ℂ)) (Set.Ioi 0) ∧
    expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n : ℝ)/x) : ℝ) : ℂ)) α =
      (∫ w in Set.Ioi (0 : ℝ),
        expSum (fun n => ((ArithmeticFunction.vonMangoldt n*
          etaTwo ((n : ℝ)/(x*w/49)) : ℝ) : ℂ)) α * ((phi w/w : ℝ) : ℂ)) ∧
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n : ℝ)/x) : ℝ) : ℂ)) α‖ ≤
      ∫ w in Set.Ioi (0 : ℝ),
        ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*
          etaTwo ((n : ℝ)/(x*w/49)) : ℝ) : ℂ)) α‖ * (phi w/w) := by sorry

end Helfgott
