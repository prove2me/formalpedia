-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianLowerZeroBarrierImmediate
-- name    : Kyprianou.Ch01.brownianLowerZeroBarrierImmediate
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T20:38:06.777208+00:00
-- url     : https://prove2.me/theorems/1cc94fd2-580f-4611-a75c-0abc5e708af2
-- title:
--   Brownian strict downcrossing of its starting level occurs immediately almost surely
-- statement:
--   For nondegenerate drifted Brownian motion started at zero, its strict first passage below its starting level has hitting-time infimum zero almost surely. Therefore every positive-discounted passageLaplace payoff equals one almost surely, is integrable, and has expectation one. This is the a=0 boundary case of Exercise 1.10(ii); the positive-barrier upper-passage transform only covers strictly positive barriers. Brownian zero-level regularity is essential to avoid a false extension to arbitrary processes.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10, Brownian strict first-passage boundary regularity.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianLowerZeroBarrierImmediate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q)
    (hX : Kyprianou.Ch01.IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Integrable (Kyprianou.Ch01.passageLaplace
      (Kyprianou.Ch01.firstLowerPassage X 0 0) q) P ∧
    (∫ ω, Kyprianou.Ch01.passageLaplace
      (Kyprianou.Ch01.firstLowerPassage X 0 0) q ω ∂P) = 1 := by sorry
