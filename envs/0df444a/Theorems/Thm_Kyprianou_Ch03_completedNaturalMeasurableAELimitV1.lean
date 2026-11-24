-- Prove2me | Theorems.Thm_Kyprianou_Ch03_completedNaturalMeasurableAELimitV1
-- name    : Kyprianou.Ch03.completedNaturalMeasurableAELimitV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T23:01:55.984698+00:00
-- url     : https://prove2.me/theorems/fcff066c-a161-4f95-ab94-884eabdc90b0
-- title:
--   Pointwise almost-sure limits of measurable states in the completed natural filtration are measurable
-- statement:
--   Pointwise almost-sure limits of measurable states in the completed natural filtration are measurable
-- source:
--   Kyprianou (2006), Exercise 3.2

import Mathlib
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.completedNaturalMeasurableAELimitV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F)
    (s : NNReal) (U : ℕ → Omega → ℝ) (V : Omega → ℝ)
    (hU : ∀ k, Measurable[F s] (U k))
    (hV : ∀ᵐ w ∂P, Tendsto (fun k => U k w) atTop (𝓝 (V w))) :
    Measurable[F s] V := by
  sorry
