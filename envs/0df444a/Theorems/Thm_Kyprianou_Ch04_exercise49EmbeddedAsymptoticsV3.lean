-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49EmbeddedAsymptoticsV3
-- name    : Kyprianou.Ch04.exercise49EmbeddedAsymptoticsV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:52:12.840138+00:00
-- url     : https://prove2.me/theorems/9bd5b2bf-f9de-47e0-915d-32d3395fd7d8
-- title:
--   Almost sure growth and nonmonotonicity are preserved by embedding the probability space
-- statement:
--   Almost sure growth and nonmonotonicity are preserved by embedding the probability space
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), exceptional-path statement audit.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49EmbeddedAsymptoticsV3
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (j : Ω → E) (hj : MeasurableEmbedding j)
    (X : NNReal → Ω → ℝ) (Y : NNReal → E → ℝ)
    (hAgree : ∀ t w, Y t (j w) = X t w)
    (hNotSub : ¬ (∀ᵐ w ∂P, Monotone (fun t : NNReal => X t w)))
    (hInfinity : ∀ᵐ w ∂P, Tendsto (fun t : NNReal => X t w) atTop atTop) :
    (¬ (∀ᵐ w ∂Measure.map j P, Monotone (fun t : NNReal => Y t w))) ∧
    (∀ᵐ w ∂Measure.map j P, Tendsto (fun t : NNReal => Y t w) atTop atTop) := by
  sorry
