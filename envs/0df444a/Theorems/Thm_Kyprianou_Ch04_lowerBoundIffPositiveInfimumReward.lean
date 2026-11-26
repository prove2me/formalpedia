-- Prove2me | Theorems.Thm_Kyprianou_Ch04_lowerBoundIffPositiveInfimumReward
-- name    : Kyprianou.Ch04.lowerBoundIffPositiveInfimumReward
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:39:41.055058+00:00
-- url     : https://prove2.me/theorems/b3ee9ba2-116a-4f7d-b82c-7ebcdca84e21
-- title:
--   Global lower bound iff positive limiting exponential
-- statement:
--   A finite lower bound gives a uniform positive exponential bound. Conversely take logs of the positive reward infimum and use the cofinal integer horizons.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.lowerBoundIffPositiveInfimumReward
    (x : NNReal → ℝ) (beta : ℝ) (hb : 0 < beta)
    (hbd : ∀ t : NNReal, BddBelow (x '' Iic t)) :
    BddBelow (range x) ↔
      0 < ⨅ n : ℕ, Real.exp (beta * sInf (x '' Iic (n : NNReal))) := by
  sorry
