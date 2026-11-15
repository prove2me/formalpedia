-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanBarrierGlobalMax
-- name    : Kyprianou.Ch01.mckeanBarrierGlobalMax
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:59:31.11922+00:00
-- url     : https://prove2.me/theorems/d4b15ae0-3392-403e-b898-086336d6c5cd
-- title:
--   McKean perpetual put barrier: global payoff maximum
-- statement:
--   For positive strike K and positive exponent phi, the perpetual put first-passage barrier payoff is maximised at b=log(K phi/(1+phi)) for every real threshold a, using the weighted exponential tangent inequality.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.10(iii), printed p. 31; original parent bea9bdc1-0ec7-448d-8142-15743baf5c77.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanBarrierGlobalMax
    (K phi x b a : ℝ) (hK : 0 < K) (hphi : 0 < phi)
    (hb : b = Real.log (K * phi / (1 + phi))) :
    (K - Real.exp a) * Real.exp (-phi * (x - a)) ≤
      (K - Real.exp b) * Real.exp (-phi * (x - b)) := by sorry
