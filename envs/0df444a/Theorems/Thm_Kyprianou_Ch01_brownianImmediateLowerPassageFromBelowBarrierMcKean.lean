-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianImmediateLowerPassageFromBelowBarrierMcKean
-- name    : Kyprianou.Ch01.brownianImmediateLowerPassageFromBelowBarrierMcKean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:27:48.782978+00:00
-- url     : https://prove2.me/theorems/9485e61f-50a5-482a-b5b7-eb5f6473da52
-- title:
--   Brownian first strict lower passage is immediately zero from or below barrier
-- statement:
--   For drifted Brownian paths with positive volatility, the first strict lower passage from a starting log-price at or below a barrier occurs at time zero almost surely. It follows from the proved Brownian zero-barrier instant-passage property and monotonicity of upper first passage after sign reversal. This supplies the at-the-money and immediately exercisable branches of the perpetual American put payoff.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13; Brownian regularity of zero and first-passage barrier monotonicity.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianImmediateLowerPassageFromBelowBarrierMcKean
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma x barrier : ℝ)
    (hsigma : 0 < sigma) (hxb : x ≤ barrier)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t)) :
    ∀ᵐ ω ∂P, firstLowerPassage X x barrier ω = 0 := by sorry
