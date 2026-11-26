-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41BinaryCadlagFlatV15
-- name    : Kyprianou.Ch04.exercise41BinaryCadlagFlatV15
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T13:08:57.393044+00:00
-- url     : https://prove2.me/theorems/f0243a54-b52b-43a1-968f-f124d8c708a5
-- title:
--   Binary cadlag path is constant across an interval with no jumps
-- statement:
--   Binary cadlag path is constant across an interval with no jumps
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41BinaryCadlagFlatV15
    (f : NNReal → ℝ)
    (hVal : ∀ u, f u = 0 ∨ f u = -1)
    (hR : ∀ u, ContinuousWithinAt f (Ici u) u)
    (hL : ∀ u, 0 < u → Tendsto f (nhdsWithin u (Iio u)) (nhds (Function.leftLim f u)))
    (s t : NNReal) (hst : s ≤ t)
    (hJump : ∀ u ∈ Ioc s t, f u - Function.leftLim f u = 0) :
    f s = f t := by
  sorry
