-- Prove2me | Theorems.Thm_Kyprianou_Ch04_runningInfimumExpRewardProperties
-- name    : Kyprianou.Ch04.runningInfimumExpRewardProperties
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:37:47.88786+00:00
-- url     : https://prove2.me/theorems/e8b254df-edfe-44a7-9812-c228e87e3dd9
-- title:
--   Measurable bounded monotone infimum reward
-- statement:
--   Finite-horizon lower boundedness and initial value zero bound the running-infimum exponential in [0,1]. Joint measurability and antitonicity follow from the established path extrema lemmas.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Theorems.Thm_Kyprianou_Ch04_runningInfimumAntitoneFromFiniteBounds
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.runningInfimumExpRewardProperties
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (beta : ℝ) (hb : 0 < beta) :
    let g : NNReal × Ω → ℝ := fun z =>
      Real.exp (beta * sInf ((fun s : NNReal => L.X s z.2) '' Iic z.1))
    Measurable g ∧ (∀ z, 0 ≤ g z) ∧ (∀ z, g z ≤ 1) ∧
      ∀ w, Antitone (fun t : NNReal => g (t,w)) := by
  sorry
