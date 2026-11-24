-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_bounded_stop_eval_measurable
-- name    : Kyprianou.Ch08.StageB.p2m810_bounded_stop_eval_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T21:58:01.555781+00:00
-- url     : https://prove2.me/theorems/ff1fef74-5540-43bd-8485-e336dc96dccb
-- title:
--   Evaluate an adapted right-continuous process at a bounded stopping time in the horizon sigma algebra, using the real-time progressive measurability theorem.
-- statement:
--   Evaluate an adapted right-continuous process at a bounded stopping time in the horizon sigma algebra, using the real-time progressive measurability theorem.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Instances.NNReal.Lemmas
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_bounded_stop_eval_measurable
    {Ω : Type} [mΩ : MeasurableSpace Ω] (F : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ)
    (hadapt : ∀ t, Measurable[F t] (X t))
    (hrc : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t)
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : ℝ≥0) (hb : ∀ ω, τ ω ≤ s) :
    Measurable[F s] (fun ω => X (τ ω) ω) := by
  sorry
