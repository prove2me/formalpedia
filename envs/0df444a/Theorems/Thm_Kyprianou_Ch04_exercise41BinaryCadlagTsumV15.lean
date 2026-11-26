-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41BinaryCadlagTsumV15
-- name    : Kyprianou.Ch04.exercise41BinaryCadlagTsumV15
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T13:08:55.532066+00:00
-- url     : https://prove2.me/theorems/766da072-8bf7-499e-ab30-6b9fba8e79d2
-- title:
--   Binary cadlag path equals the sum of its finitely supported jumps
-- statement:
--   Binary cadlag path equals the sum of its finitely supported jumps
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41BinaryCadlagTsumV15
    (f : NNReal → ℝ) (h0 : f 0 = 0)
    (hVal : ∀ u, f u = 0 ∨ f u = -1)
    (hLVal : ∀ u, 0 < u → Function.leftLim f u = 0 ∨ Function.leftLim f u = -1)
    (hR : ∀ u, ContinuousWithinAt f (Ici u) u)
    (hL : ∀ u, 0 < u → Tendsto f (nhdsWithin u (Iio u)) (nhds (Function.leftLim f u)))
    (T : NNReal) :
    Set.Finite (Function.support (fun u : Ioc (0 : NNReal) T =>
      f u - Function.leftLim f u)) ∧
    f T = ∑' u : Ioc (0 : NNReal) T, (f u - Function.leftLim f u) := by
  sorry
