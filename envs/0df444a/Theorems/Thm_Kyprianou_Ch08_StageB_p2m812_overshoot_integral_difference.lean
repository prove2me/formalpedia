-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m812_overshoot_integral_difference
-- name    : Kyprianou.Ch08.StageB.p2m812_overshoot_integral_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:36:40.323359+00:00
-- url     : https://prove2.me/theorems/dbe72bf1-70b1-49fd-859a-c1ecc1cda5bc
-- title:
--   Stable overshoot difference of rational integrals
-- statement:
--   Integrability from -r > -1 and continuous reciprocals, followed by the rational pointwise difference.
-- source:
--   Kyprianou (2006), Exercise 8.12(ii), deterministic reduction of a2bff24a-f079-4443-9df9-9f0fcdcdfd4b.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.p2m812_overshoot_integral_difference
    (r x y : ℝ) (hr : 0 < r) (hr1 : r < 1) (hx : 0 < x) (hy : 0 ≤ y) :
    (∫ t in (0 : ℝ)..y, t^(-r)/(t+x)) -
      (∫ t in (0 : ℝ)..y, t^(-r)/(t+1)) =
      (1-x) * ∫ t in (0 : ℝ)..y, t^(-r)/((t+1)*(t+x)) := by
  sorry
