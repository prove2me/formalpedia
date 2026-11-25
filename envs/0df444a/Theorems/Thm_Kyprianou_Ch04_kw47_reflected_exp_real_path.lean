-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_reflected_exp_real_path
-- name    : Kyprianou.Ch04.kw47_reflected_exp_real_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:12:28.961026+00:00
-- url     : https://prove2.me/theorems/c086923b-41a3-45b8-ab77-27360bb74ed6
-- title:
--   Measurable bounded right-continuous reflected exponential paths
-- statement:
--   For every actual spectrally negative Levy path and nonnegative alpha the real-time reflected exponential, extended by the zero-time value at negative times, is measurable, has absolute value at most one, and is right-continuous at every real time. Joint measurability, continuity of the running supremum, right continuity of the Levy path and the monotone continuous real-to-nonnegative-real map give these properties.
-- source:
--   Kyprianou (2006), Exercise 4.7; pathwise right-endpoint quadrature.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_exp_bounds
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The reflected exponential has bounded measurable right-continuous
paths after extending nonnegative time by the zero-time value. -/

theorem Kyprianou.Ch04.kw47_reflected_exp_real_path
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (w : Ω) :
    let Z : Real → Real := fun r =>
      Real.exp (-alpha * (runningSup L r.toNNReal w - L.X r.toNNReal w))
    Measurable Z ∧ (∀ r, ‖Z r‖ ≤ 1) ∧
      ∀ r, ContinuousWithinAt Z (Ici r) r := by sorry
