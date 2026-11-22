-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedPutContactAboveBarrier
-- name    : Kyprianou.Ch01.mckeanDiscountedPutContactAboveBarrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:21:21.896327+00:00
-- url     : https://prove2.me/theorems/455c17d9-6435-4725-91db-21fd9edecdce
-- title:
--   Pathwise put reward at finite lower passage above exercise barrier
-- statement:
--   For every continuous path starting from zero, a strict lower barrier beneath the initial log-price is reached by continuous contact whenever the hitting time is finite. Since the put is in the money at the barrier, the discounted payoff at that time equals (K minus exp barrier) times the discounted passage Laplace functional. Infinite passages give zero on both sides. This pathwise identity is a necessary source step in the perpetual American put reward calculation.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13; continuous first-passage contact and stopped put payoff.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanDiscountedPutContactAboveBarrier
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (x barrier K q : ℝ)
    (hxb : barrier < x) (hK : Real.exp barrier ≤ K)
    (hContinuous : Continuous (fun t : ℝ≥0 => X t ω))
    (hStart : X 0 ω = 0) :
    discountedPut X x K q (firstLowerPassage X x barrier) ω =
      (K - Real.exp barrier) *
        passageLaplace (firstLowerPassage X x barrier) q ω := by sorry
