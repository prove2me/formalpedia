-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_bounded_stop_parameter_history
-- name    : Kyprianou.Ch08.StageB.p2m810_bounded_stop_parameter_history
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T22:08:28.944619+00:00
-- url     : https://prove2.me/theorems/c375d600-5e0a-44f3-9de3-5fcf5bee10cd
-- title:
--   A bounded stopping time and its process value form a measurable stopped-history parameter. Use evaluation at min(τ,s) on the event τ≤s.
-- statement:
--   A bounded stopping time and its process value form a measurable stopped-history parameter. Use evaluation at min(τ,s) on the event τ≤s.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Probability.Process.Stopping
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_bounded_stop_parameter_history
    {Ω : Type} [mΩ : MeasurableSpace Ω] (F : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ)
    (hadapt : ∀ t, Measurable[F t] (X t))
    (hrc : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t)
    (τ : Ω → ℝ≥0) (hτ : MeasureTheory.IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T) :
    Measurable (fun ω => (τ ω,X (τ ω) ω)) ∧
      ∀ B : Set (ℝ≥0 × ℝ), MeasurableSet B → ∀ s : ℝ≥0,
        MeasurableSet[F s] ({ω | (τ ω,X (τ ω) ω) ∈ B} ∩ {ω | τ ω ≤ s}) := by
  sorry
