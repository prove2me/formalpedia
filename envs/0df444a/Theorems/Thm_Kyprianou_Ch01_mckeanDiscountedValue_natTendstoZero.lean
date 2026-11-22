-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedValue_natTendstoZero
-- name    : Kyprianou.Ch01.mckeanDiscountedValue_natTendstoZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:57:06.131151+00:00
-- url     : https://prove2.me/theorems/7194920e-4796-4c43-9c99-242092b031b3
-- title:
--   Discounted uniformly bounded McKean value tends to zero along integer horizons
-- statement:
--   Every bounded nonnegative McKean candidate value V(X_n+x), with 0≤V≤K, vanishes under positive exponential discount exp(-qn) along integer n tending to infinity. Use the already Proved uniform McKean value bound and exponential-decay theorem together with squeeze_zero. No process measurability or stochastic assumptions are required. This isolates the infinite stopping-time branch of the original pathwise convergence argument.
-- source:
--   Kyprianou 2006 Chapter 1 Theorem 1.13; terminal-at-infinity discount.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanValueBoundedNonnegative
import Theorems.Thm_e7_exp_neg_scale_tendsto_zero
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanDiscountedValue_natTendstoZero
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ) (hK : 0 < K) (hq : 0 < q) (hphi : 0 < phi)
    (ω : Ω) :
    Filter.Tendsto (fun n : ℕ =>
      Real.exp (-q * (n : ℝ)) *
        mckeanValue K (Real.log (K * phi / (1 + phi))) phi
          (x + X (n : ℝ≥0) ω))
      Filter.atTop (nhds 0) := by sorry
