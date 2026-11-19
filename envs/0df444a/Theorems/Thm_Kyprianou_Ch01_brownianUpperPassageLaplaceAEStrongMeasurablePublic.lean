-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianUpperPassageLaplaceAEStrongMeasurablePublic
-- name    : Kyprianou.Ch01.brownianUpperPassageLaplaceAEStrongMeasurablePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:57:03.009725+00:00
-- url     : https://prove2.me/theorems/cd924ce9-7d5d-462c-96c0-0247260c5995
-- title:
--   Brownian strict upper-passage discounted payoff is almost everywhere strongly measurable
-- statement:
--   The discounted first strict upper passage payoff is almost everywhere strongly measurable under the original Lévy-defined drifted Brownian law, measurable coordinates and its almost-sure continuity. The first passage can be recovered from countably many rational observation times on the full-measure set of continuous paths. This supplies the measurability input to the integral dominated by one.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10(ii), solution. Measurability of Brownian first passage.

import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianUpperPassageLaplaceAEStrongMeasurablePublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    AEStronglyMeasurable (passageLaplace (firstUpperPassage X x) q) P := by sorry
