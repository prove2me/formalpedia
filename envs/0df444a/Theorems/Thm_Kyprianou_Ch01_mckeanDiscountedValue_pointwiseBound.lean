-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedValue_pointwiseBound
-- name    : Kyprianou.Ch01.mckeanDiscountedValue_pointwiseBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:19:44.090079+00:00
-- url     : https://prove2.me/theorems/bceaf047-b460-401c-ba6d-22cf0d4aecec
-- title:
--   Discounted McKean value is pathwise nonnegative and bounded by the strike
-- statement:
--   At every time and on every sample point, the discounted explicit McKean candidate is between zero and the strike K for any positive discount q and positive value exponent phi. Use the already Proved uniform value bound 0≤V≤K, the nonnegativity of the exponential discount, and q>0 together with t≥0 to bound exp(-qt)≤1. This provides a uniform pathwise majorant for dominated convergence and ensures nonnegative discounted optional stopping processes.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13; bounded nonnegative discounted candidate value.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanValueBoundedNonnegative
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanDiscountedValue_pointwiseBound
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ) (hK : 0 < K) (hq : 0 < q) (hphi : 0 < phi)
    (t : ℝ≥0) (ω : Ω) :
    let barrier := Real.log (K * phi / (1 + phi))
    0 ≤ Real.exp (-q * (t : ℝ)) *
      mckeanValue K barrier phi (x + X t ω) ∧
    Real.exp (-q * (t : ℝ)) *
      mckeanValue K barrier phi (x + X t ω) ≤ K := by sorry
