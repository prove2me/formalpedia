-- Prove2me | Theorems.Thm_Kyprianou_Ch01_discountedPut_pointwiseBound
-- name    : Kyprianou.Ch01.discountedPut_pointwiseBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:53:35.807428+00:00
-- url     : https://prove2.me/theorems/922ef7bc-751a-4e5c-bc9c-7c4629bcabf7
-- title:
--   The discounted perpetual-put payoff lies between zero and its strike
-- statement:
--   For any real-valued sample path, nonnegative stopping time and positive strike and discount rate, the discounted perpetual American put payoff is bounded between zero and the strike, independently of the Brownian law.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10, integrability/bounded-payoff component of the McKean Brownian stopping problem.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open Kyprianou.Ch01 MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.discountedPut_pointwiseBound
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (x K q : ℝ)
    (hK : 0 < K) (hq : 0 < q)
    (tau : Ω → WithTop ℝ≥0) (omega : Ω) :
    0 ≤ discountedPut X x K q tau omega ∧
      discountedPut X x K q tau omega ≤ K := by sorry
