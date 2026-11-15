-- Prove2me | Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
-- name    : Kyprianou.Ch01.cadlag_runningSup_bddAbove
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:34:56.623079+00:00
-- url     : https://prove2.me/theorems/a92cc0c0-725a-4732-a803-82da495cb71b
-- title:
--   A cadlag real path has bounded running range on each finite horizon
-- statement:
--   A cadlag real-valued function on nonnegative time has a bounded-above image on every compact time interval. This is the pathwise compactness lemma required to control running suprema of risk surplus and workloads.
-- source:
--   Kyprianou (2006), Chapter 1, risk and queue paths; derived from the established AvramDividend one-sided-limits boundedness result.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc
open Filter MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.cadlag_runningSup_bddAbove
    (f : ℝ≥0 → ℝ) (hf : ProbabilityTheory.IsCadlag f) (T : ℝ≥0) :
    BddAbove {z : ℝ | ∃ s : ℝ≥0, s ≤ T ∧ z = f s} := by sorry
