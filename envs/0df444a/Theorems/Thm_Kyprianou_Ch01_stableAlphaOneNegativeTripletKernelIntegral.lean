-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneNegativeTripletKernelIntegral
-- name    : Kyprianou.Ch01.stableAlphaOneNegativeTripletKernelIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:06:46.952273+00:00
-- url     : https://prove2.me/theorems/28587452-b115-4e36-af02-732c1be305fa
-- title:
--   Negative-halfline index-one compensated Lévy integral reflects to negative-frequency positive oscillatory kernel
-- statement:
--   Reflect the negative-halfline Lévy density and compensated integrand to positive radii, using the proved stableAlphaOneLevyCompensatorReflection. Nonnegative cneg is essential for ENNReal.ofReal density and the result uses the original cutoff.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4: original two-sided Levy triplet index-one compensator.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneNegativeTripletKernelIntegral
    (cneg xi : ℝ) (hcneg : 0 ≤ cneg) :
    let alpha : ℝ := 1
    let muNeg : Measure ℝ := (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)))
    let F : ℝ → ℂ := (fun z : ℝ =>
      ∫ r in Set.Ioi (0 : ℝ),
        ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
            Complex.I * (((z * r : ℝ) : ℂ)) *
              (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume);
    -(∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muNeg) =
      (cneg : ℂ) * F (-xi) := by sorry
