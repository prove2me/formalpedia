-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49StoppedDeficitFutureProductV1
-- name    : Kyprianou.Ch04.exercise49StoppedDeficitFutureProductV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:54:49.36027+00:00
-- url     : https://prove2.me/theorems/32aee3e8-8e76-48c4-b4d5-f07fc4bd2db2
-- title:
--   First strict negative passage: restricted joint law of deficit and future path
-- statement:
--   First strict negative passage: restricted joint law of deficit and future path
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49StoppedDeficitFutureProductV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ w, IsCadlag (fun t => X t w))
    (τ : Ω → WithTop NNReal)
    (hτ : ∀ w, τ w = sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ X t w < 0})
    (hτm : Measurable τ) (f : Ω → NNReal) (hf : Measurable f)
    (he : ∀ w, τ w ≠ ⊤ → τ w = (f w : WithTop NNReal)) :
    let D : Set Ω := {w | τ w ≠ ⊤}
    let I : Ω → ℝ := fun w => -X (f w) w
    let Y : Ω → (NNReal → ℝ) := fun w u => X (f w + u) w - X (f w) w
    Measure.map (fun w => (I w, Y w)) (P.restrict D) =
      (Measure.map I (P.restrict D)).prod (Measure.map (fun w u => X u w) P) := by
  sorry
