-- Prove2me | Theorems.Thm_Kyprianou_Ch01_isLevyProcess_lift_productSnd
-- name    : Kyprianou.Ch01.isLevyProcess_lift_productSnd
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:02:53.106953+00:00
-- url     : https://prove2.me/theorems/8be08c1f-ee14-4cf1-bc86-082d4f4c1db5
-- title:
--   Genuine Lévy processes lift to the second coordinate of an independent product probability space
-- statement:
--   For any genuine measurable-time-marginal Lévy process Y on a probability space Q and an independent probability factor P, the coordinate lift Y_t(ω₂) under P ⊗ Q remains a genuine LeanLevy Lévy process, preserving strict zero start, mutually independent finite-grid increments, equal-lag stationary laws and almost-sure càdlàg sample paths. Proof uses the independently established second-coordinate transfer results, plus a.e. transfer of pathwise regularity by the measure-preserving second projection.
-- source:
--   LeanLevy_Processes_LevyProcess; pinned Mathlib ae_of_ae_map and measurePreserving_snd; Kyprianou Chapter 1 Theorem 1.6.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.isLevyProcess_lift_productSnd
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Y : ℝ≥0 → Λ → ℝ)
    (h : IsLevyProcess Y Q)
    (hYm : ∀ t, Measurable (Y t)) :
    IsLevyProcess (fun t (p : Ω × Λ) => Y t p.2) (P.prod Q) := by
  sorry
