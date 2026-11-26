-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stationaryLawObstructedByVanishingDrawdown
-- name    : Kyprianou.Ch04.stationaryLawObstructedByVanishingDrawdown
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:16:26.941496+00:00
-- url     : https://prove2.me/theorems/126b8156-8895-5c24-81ef-9402a834227a
-- title:
--   Vanishing drawdown transform excludes stationary probability
-- statement:
--   Use the strictly positive bounded continuous test exp(-max(0,x)). Its stationary expectation is strictly positive but bounded by the vanishing drawdown transform, a contradiction.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.stationaryLawObstructedByVanishingDrawdown
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : NNReal → Ω → ℝ) (W : NNReal → ℝ → Ω → ℝ)
    (hD : ∀ t, Measurable (D t)) (hD0 : ∀ t z, 0 ≤ D t z)
    (hW : ∀ t w z, 0 ≤ w → D t z ≤ W t w z)
    (hlim : Tendsto (fun t => ∫ z, Real.exp (-D t z) ∂P) atTop (nhds 0)) :
    ¬ ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Ici 0) = 1 ∧
      ∀ (t : NNReal) (f : BoundedContinuousFunction ℝ ℝ),
        (∫ w in Ici 0, (∫ z, f (W t w z) ∂P) ∂μ) = ∫ w, f w ∂μ := by
  sorry
