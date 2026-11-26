-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41BinaryCadlagFiniteV15
-- name    : Kyprianou.Ch04.exercise41BinaryCadlagFiniteV15
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:08:56.251468+00:00
-- url     : https://prove2.me/theorems/72bb8c22-232c-4c09-8b12-bcc7d5f217a6
-- title:
--   The actual jump support of a binary cadlag path is finite on compact time intervals
-- statement:
--   The actual jump support of a binary cadlag path is finite on compact time intervals
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41BinaryCadlagFiniteV15
    (f : NNReal → ℝ)
    (hVal : ∀ u, f u = 0 ∨ f u = -1)
    (hLVal : ∀ u, 0 < u → Function.leftLim f u = 0 ∨ Function.leftLim f u = -1)
    (hR : ∀ u, ContinuousWithinAt f (Ici u) u)
    (hL : ∀ u, 0 < u → Tendsto f (nhdsWithin u (Iio u)) (nhds (Function.leftLim f u)))
    (T : NNReal) :
    Set.Finite {u : NNReal | 0 < u ∧ u ≤ T ∧ f u - Function.leftLim f u ≠ 0} := by
  sorry
