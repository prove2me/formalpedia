-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m812_overshoot_scaled_integral
-- name    : Kyprianou.Ch08.StageB.p2m812_overshoot_scaled_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:36:42.288614+00:00
-- url     : https://prove2.me/theorems/2fc475a3-17c1-40c2-b539-8061e4324521
-- title:
--   Stable overshoot integral under spatial scaling
-- statement:
--   Change variables, using the positive spatial scale x.
-- source:
--   Kyprianou (2006), Exercise 8.12(ii), deterministic reduction of a2bff24a-f079-4443-9df9-9f0fcdcdfd4b.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.p2m812_overshoot_scaled_integral
    (r x y : ℝ) (hr : 0 < r) (hr1 : r < 1) (hx : 0 < x) (hy : 0 ≤ y) :
    (∫ t in (0 : ℝ)..y/x, t^(-r)/(1+t)) =
      x^r * ∫ t in (0 : ℝ)..y, t^(-r)/(t+x) := by
  sorry
