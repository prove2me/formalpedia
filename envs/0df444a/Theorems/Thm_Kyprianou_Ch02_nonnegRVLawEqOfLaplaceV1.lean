-- Prove2me | Theorems.Thm_Kyprianou_Ch02_nonnegRVLawEqOfLaplaceV1
-- name    : Kyprianou.Ch02.nonnegRVLawEqOfLaplaceV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T00:02:23.194082+00:00
-- url     : https://prove2.me/theorems/f9c180c5-f944-42d6-877a-1d101a931293
-- title:
--   Nonnegative random variables with equal Laplace transforms have the same law
-- statement:
--   Apply the proved positive exponential-moment uniqueness theorem to the laws of -A and -B, using boundedness of all positive exponential moments, then negate again.
-- source:
--   Kyprianou (2006), Exercise 2.8, independence of Jordan variation components.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.nonnegRVLawEqOfLaplaceV1
    {Ω : Type} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (A B : Ω → ℝ) (hmA : Measurable A) (hmB : Measurable B)
    (hnA : ∀ ω, 0 ≤ A ω) (hnB : ∀ ω, 0 ≤ B ω)
    (h : ∀ s : ℝ, 0 < s →
      (∫ ω, Real.exp (-(s*A ω)) ∂P) = ∫ ω, Real.exp (-(s*B ω)) ∂Q) :
    P.map A = Q.map B := by sorry
