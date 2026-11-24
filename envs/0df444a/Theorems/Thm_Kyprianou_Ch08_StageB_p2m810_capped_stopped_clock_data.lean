-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_capped_stopped_clock_data
-- name    : Kyprianou.Ch08.StageB.p2m810_capped_stopped_clock_data
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T22:08:28.345221+00:00
-- url     : https://prove2.me/theorems/4083688f-cfb3-4397-a163-badd3d91177a
-- title:
--   The capped clock min(τ,n) is a finite stopping time, agrees with the original clock on the cap event, and that event is a stopped-history event.
-- statement:
--   The capped clock min(τ,n) is a finite stopping time, agrees with the original clock on the cap event, and that event is a stopped-history event.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Probability.Process.Stopping
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_capped_stopped_clock_data
    {Ω : Type} [mΩ : MeasurableSpace Ω] (F : Filtration ℝ≥0 mΩ)
    (τ : Ω → WithTop ℝ≥0) (hτ : MeasureTheory.IsStoppingTime F τ) (n : ℝ≥0) :
    let ρ := fun ω => WithTop.untopD 0 (min (τ ω) (n : WithTop ℝ≥0))
    MeasureTheory.IsStoppingTime F (fun ω => (ρ ω : WithTop ℝ≥0)) ∧
      (∀ ω, ρ ω ≤ n) ∧
      (∀ ω, τ ω ≤ (n : WithTop ℝ≥0) → (ρ ω : WithTop ℝ≥0) = τ ω) ∧
      ∀ s : ℝ≥0,
        MeasurableSet[F s] ({ω | τ ω ≤ (n : WithTop ℝ≥0)} ∩ {ω | ρ ω ≤ s}) := by
  sorry
