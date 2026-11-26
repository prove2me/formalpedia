-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41WindowStartGeometryV25
-- name    : Kyprianou.Ch04.exercise41WindowStartGeometryV25
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:08:54.241384+00:00
-- url     : https://prove2.me/theorems/7e2f33c6-661e-48ac-a8e3-46ca143dbc6b
-- title:
--   A short window starting shortly before a positive contact stays within a prescribed neighbourhood
-- statement:
--   A short window starting shortly before a positive contact stays within a prescribed neighbourhood
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41WindowStartGeometryV25
    (s e h : NNReal) (hs : 0 < s) (hh : 0 < h) (hhe : h < e) (hhs : h < s)
    (r : ℝ) (hr : r ∈ Ioo ((s : ℝ)-(h : ℝ)) (s : ℝ)) :
    0 ≤ r ∧ r.toNNReal ≤ s ∧ s < r.toNNReal+h ∧
      Icc r.toNNReal (r.toNNReal+h) ⊆ Icc (s-e) (s+e) := by
  sorry
