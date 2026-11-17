-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricToLogarithmicParameters
-- name    : Kyprianou.Ch01.geometricToLogarithmicParameters
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:18:56.498287+00:00
-- url     : https://prove2.me/theorems/12f318eb-a6d0-4a56-872b-889c5d9a3347
-- title:
--   Strict geometric parameter yields valid logarithmic-jump probability and positive Poisson rate
-- statement:
--   For 0<p<1, the jump-series parameter q=1−p lies strictly in (0,1) and the associated compound-Poisson intensity −log(p) is strictly positive. This is the exact admissibility condition for Kyprianou's strict geometric compound-Poisson representation.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(i).

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Geometric
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricToLogarithmicParameters
    (p : unitInterval.Elem) (hp : p ≠ 0)
    (hp1 : (p : ℝ) < 1) :
    0 < 1 - (p : ℝ) ∧
    1 - (p : ℝ) < 1 ∧
    0 < -Real.log (p : ℝ) := by
  sorry
