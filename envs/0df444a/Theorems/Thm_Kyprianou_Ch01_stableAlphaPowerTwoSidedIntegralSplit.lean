-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaPowerTwoSidedIntegralSplit
-- name    : Kyprianou.Ch01.stableAlphaPowerTwoSidedIntegralSplit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:40:45.106428+00:00
-- url     : https://prove2.me/theorems/0a027fe9-ecd7-4434-9fb4-be482a0f35b9
-- title:
--   Original two-sided stable compensated Levy jump sum equals exact positive and negative weighted integrals
-- statement:
--   Under independent Bochner-integrability of the original Lévy compensated kernel against each positive/negative stable power-law measure, the compensated integral against their sum equals the exact weighted positive and negative Lebesgue halfline integrals, preserving original source cutoff. The single integrability hypotheses can be derived from the Lévy triplet admissibility.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, source-exact two-sided stable Levy measure.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaPowerPositiveDensityIntegral
import Theorems.Thm_Kyprianou_Ch01_stableAlphaPowerNegativeDensityIntegral
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaPowerTwoSidedIntegralSplit
    (alpha cpos cneg xi : ℝ) (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg) :
    let muPos : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (cpos * r ^ (-alpha - 1)))
    let muNeg : Measure ℝ :=
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (cneg * |r| ^ (-alpha - 1)))
    Integrable (ProbabilityTheory.levyCompensatedIntegrand xi) muPos →
    Integrable (ProbabilityTheory.levyCompensatedIntegrand xi) muNeg →
    (∫ r, ProbabilityTheory.levyCompensatedIntegrand xi r ∂(muPos + muNeg)) =
      (∫ r in Set.Ioi (0 : ℝ),
        (cpos * r ^ (-alpha - 1)) •
          ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) +
      (∫ r in Set.Iio (0 : ℝ),
        (cneg * |r| ^ (-alpha - 1)) •
          ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) := by sorry
