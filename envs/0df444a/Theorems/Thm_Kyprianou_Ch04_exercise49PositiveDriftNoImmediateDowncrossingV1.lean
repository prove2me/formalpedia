-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49PositiveDriftNoImmediateDowncrossingV1
-- name    : Kyprianou.Ch04.exercise49PositiveDriftNoImmediateDowncrossingV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:30:49.771936+00:00
-- url     : https://prove2.me/theorems/55d30e01-05a2-497c-acad-6a9f9edf5e6e
-- title:
--   Positive small-time slope excludes immediate downward passage
-- statement:
--   If a real path x(t) satisfies x(t)/t → d > 0 as t approaches zero from the right, the infimum of all its strictly positive negative-passage times, in WithTop NNReal, is strictly positive.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.9(ii), printed page 109.

import Mathlib
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49PositiveDriftNoImmediateDowncrossingV1
    (x : NNReal → ℝ) (d : ℝ) (hd : 0 < d)
    (h : Tendsto (fun t : NNReal => x t / (t : ℝ))
      (nhdsWithin (0 : NNReal) (Ioi 0)) (nhds d)) :
    (0 : WithTop NNReal) <
      sInf {u : WithTop NNReal |
        ∃ t : NNReal, u = ↑t ∧ 0 < t ∧ x t < 0} := by
  sorry
