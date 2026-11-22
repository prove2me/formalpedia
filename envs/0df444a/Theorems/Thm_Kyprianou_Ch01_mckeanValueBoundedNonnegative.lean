-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanValueBoundedNonnegative
-- name    : Kyprianou.Ch01.mckeanValueBoundedNonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:41:01.228809+00:00
-- url     : https://prove2.me/theorems/755b47a8-61a6-47bf-9dc4-c60b4831ab5b
-- title:
--   McKean put value lies between zero and strike for every log-price
-- statement:
--   For positive strike K and positive Brownian passage exponent phi, the explicit McKean perpetual put candidate value is nonnegative and at most the strike K for every log-price. Below the optimal barrier it equals K minus exp y; above the barrier it is the nonnegative continuation factor (K minus exp barrier) times exp minus phi times distance, at most K. This uniform bound is used to justify dominated convergence in continuous-time optional sampling of the discounted candidate value.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13; elementary bounds for Brownian perpetual American put value.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanValueBoundedNonnegative
    (K phi y : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    0 ≤ mckeanValue K barrier phi y ∧
      mckeanValue K barrier phi y ≤ K := by sorry
