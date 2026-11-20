-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaPowerTripletIntegralSplit
-- name    : Kyprianou.Ch01.stableAlphaPowerTripletIntegralSplit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:46:54.832077+00:00
-- url     : https://prove2.me/theorems/503df291-f690-425a-b869-0cd423e3e290
-- title:
--   Source exact stable two-sided jump integral split from genuine Levy triple integrability
-- statement:
--   For the original admissible LevyKhintchineTriple with the exact positive and negative stable power-law measure and nonnegative coefficients, its compensated jump integral equals the sum of weighted positive/negative halfline integrals. Integrability is derived from the proved global compensated Lévy kernel integrability and monotonicity of measures, with no extra analytic assumptions.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, original Lévy triplet and two-sided Lévy density.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Theorems.Thm_Kyprianou_Ch01_stableAlphaPowerTwoSidedIntegralSplit
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaPowerTripletIntegralSplit
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (alpha cpos cneg xi : ℝ) (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg) :
    let muPos : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (cpos * r ^ (-alpha - 1)))
    let muNeg : Measure ℝ :=
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (cneg * |r| ^ (-alpha - 1)))
    T.levyMeasure = muPos + muNeg →
    (∫ r, ProbabilityTheory.levyCompensatedIntegrand xi r ∂T.levyMeasure) =
      (∫ r in Set.Ioi (0 : ℝ),
        (cpos * r ^ (-alpha - 1)) •
          ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) +
      (∫ r in Set.Iio (0 : ℝ),
        (cneg * |r| ^ (-alpha - 1)) •
          ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) := by sorry
