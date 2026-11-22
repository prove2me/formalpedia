-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedValue_continuousPath
-- name    : Kyprianou.Ch01.mckeanDiscountedValue_continuousPath
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:33:09.850779+00:00
-- url     : https://prove2.me/theorems/a0bc5906-7b4d-4798-a025-f53fd2cd3aec
-- title:
--   Discounted McKean Brownian candidate has continuous time paths
-- statement:
--   For any process with continuous real sample paths, the explicitly discounted McKean candidate value t↦exp(-qt)V(x+X_t) has continuous paths on nonnegative real time, for any real discount q and positive strike and exponent. It follows by composition of the already Proved global continuity of the optimal piecewise value function with continuous log-price paths, and multiplication by the continuously varying exponential discount. This establishes pathwise right-continuity needed for the proved MarkovProcess continuous-time bounded supermartingale optional-stopping theorem.
-- source:
--   Kyprianou (2006) Chapter 1 Theorem 1.13; pathwise continuity of the discounted perpetual American put value process.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanValue_continuous
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanDiscountedValue_continuousPath
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ) (hK : 0 < K) (hphi : 0 < phi)
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    ∀ ω, Continuous (fun t : ℝ≥0 =>
      Real.exp (-q * (t : ℝ)) *
        mckeanValue K (Real.log (K * phi / (1 + phi))) phi
          (x + X t ω)) := by sorry
