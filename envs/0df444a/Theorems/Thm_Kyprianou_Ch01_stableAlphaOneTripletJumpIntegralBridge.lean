-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneTripletJumpIntegralBridge
-- name    : Kyprianou.Ch01.stableAlphaOneTripletJumpIntegralBridge
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T12:48:01.394251+00:00
-- url     : https://prove2.me/theorems/8499aaaa-f491-4681-a003-0dce855ad28e
-- title:
--   Exact signed two-sided alpha-one stable Lévy jump integral decomposition
-- statement:
--   For nonnegative positive and negative jump intensities, the compensated Lévy–Khintchine complex jump integral under the source alpha-one two-sided Lévy measure is exactly minus cpos times the Kyprianou positive-half-line complex kernel integral at frequency xi and minus cneg times the reflected-frequency integral at −xi. This is the full measure-decomposition, sign-convention, and negative-jump substitution obligation needed for the remaining original Chapter 1 stableLevyExponentFormIndexOne milestone; it retains full integrability rather than assuming formal algebra of divergent integrals.
-- source:
--   Kyprianou (2006), Chapter 1, equation (1.8), stable index-one Lévy measure and Lévy–Khintchine triple.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneTripletJumpIntegralBridge
    (cpos cneg : ℝ) (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg) :
    let alpha : ℝ := 1
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))) +
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)))
    ∀ xi : ℝ,
      (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂Pi) =
        -((cpos : ℂ) * (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) +
        Complex.I * (((xi * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume) +
          (cneg : ℂ) * (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * ((((-xi) * r : ℝ) : ℂ))) +
        Complex.I * ((((-xi) * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume)) := by
  sorry
