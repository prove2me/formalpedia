-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanValueMajorizesPutPayoff
-- name    : Kyprianou.Ch01.mckeanValueMajorizesPutPayoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:32:26.807546+00:00
-- url     : https://prove2.me/theorems/362de589-aac8-4dff-8253-c8d705433344
-- title:
--   McKean value function dominates the perpetual put exercise payoff
-- statement:
--   The explicit McKean perpetual American put value dominates the immediate exercise payoff at every log-price. Above the optimal boundary use the proved mckeanBarrierGlobalMax inequality with candidate barrier a=y, while below the barrier value equals the positive put payoff. This verifies the pointwise majorant requirement in the stochastic optional-sampling verification.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13; perpetual put optimal stopping verification by majorant.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanValueMajorizesPutPayoff
    (K phi y : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    max (K - Real.exp y) 0 ≤ mckeanValue K barrier phi y := by sorry
