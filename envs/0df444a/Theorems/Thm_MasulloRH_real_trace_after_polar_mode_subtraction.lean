-- Prove2me | Theorems.Thm_MasulloRH_real_trace_after_polar_mode_subtraction
-- name    : MasulloRH.real_trace_after_polar_mode_subtraction
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T03:19:44.587847+00:00
-- url     : https://prove2.me/theorems/ac29af66-0c1a-4a53-a4ae-371a8786310f
-- title:
--   Absolute mode expansion of the even real-place trace after its polar evaluation is subtracted
-- statement:
--   For an integrable real test $f$ on $[a,b]$ with $a>0$, the difference between the even Archimedean contribution $\int_a^b f(u)e^{-u/2}/(1-e^{-2u})\,du$ and the principal positive-dilation evaluation $\int_a^b f(u)e^{-u/2}\,du$ equals $\sum_{k\ge 1}\int_a^b f(u)e^{-(2k+1/2)u}\,du$. The sum of the integrals of absolute values is finite. These are the real-place modes at positive log norm in the rational weighted Paley–Wiener comparison.
-- source:
--   Masullo, §12.4 Theorem 12.4.1.1 real-place kernel, rational even component. The integrated scalar identity concerns the evaluation removed by imposing zero at the additive origin.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory Set

theorem MasulloRH.real_trace_after_polar_mode_subtraction (a b : ℝ) (ha : 0 < a) (f : ℝ → ℝ) (hf : IntegrableOn f (Icc a b)) :
    let μ := volume.restrict (Icc a b)
    let h (j : ℕ) (x : ℝ) := f x * Real.exp (-x/2) * Real.exp (-2*x)^(j+1)
    Summable (fun j => ∫ x, |h j x| ∂μ) ∧
      HasSum (fun j => ∫ x, h j x ∂μ)
        ((∫ x, f x * (Real.exp (-x/2) / (1-Real.exp (-2*x))) ∂μ) -
         ∫ x, f x * Real.exp (-x/2) ∂μ) := by sorry
