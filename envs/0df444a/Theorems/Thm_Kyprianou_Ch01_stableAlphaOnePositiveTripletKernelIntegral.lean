-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOnePositiveTripletKernelIntegral
-- name    : Kyprianou.Ch01.stableAlphaOnePositiveTripletKernelIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:06:47.608087+00:00
-- url     : https://prove2.me/theorems/248266d2-877d-4fa7-a91b-cfbfd984e3ae
-- title:
--   Positive-halfline index-one compensated Lévy integral equals positive oscillatory kernel
-- statement:
--   Use the exact nonnegative positive-halfline power-law density, Mathlib change of density, and the proved stableAlphaOnePositiveLevyCompensatorBridge. The pointwise 1/r² kernel and truncation are unchanged.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4: original two-sided Levy triplet index-one compensator.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOnePositiveTripletKernelIntegral
    (cpos xi : ℝ) (hcpos : 0 ≤ cpos) :
    let alpha : ℝ := 1
    let muPos : Measure ℝ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1)))
    let F : ℝ → ℂ := (fun z : ℝ =>
      ∫ r in Set.Ioi (0 : ℝ),
        ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
            Complex.I * (((z * r : ℝ) : ℂ)) *
              (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume);
    -(∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muPos) =
      (cpos : ℂ) * F xi := by sorry
