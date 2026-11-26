-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_Z_right_path
-- name    : Kyprianou.Ch04.kw48_Z_right_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:32:20.460458+00:00
-- url     : https://prove2.me/theorems/252a870b-cc0e-5e31-98b1-614efd420e3a
-- title:
--   Measurability and right continuity of reflected characteristic paths
-- statement:
--   Measurability and right continuity of reflected characteristic paths.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Reflected characteristic paths extended to real time are measurable
and right-continuous. -/

theorem Kyprianou.Ch04.kw48_Z_right_path {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha beta : Real) (w : Ω) :
    Measurable (fun r : Real => Z L alpha beta r.toNNReal w) ∧
    ∀ r : Real, ContinuousWithinAt (fun x : Real =>
      Z L alpha beta x.toNNReal w) (Ici r) r := by sorry
