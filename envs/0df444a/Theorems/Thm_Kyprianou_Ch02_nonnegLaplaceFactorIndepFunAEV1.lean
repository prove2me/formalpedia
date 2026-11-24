-- Prove2me | Theorems.Thm_Kyprianou_Ch02_nonnegLaplaceFactorIndepFunAEV1
-- name    : Kyprianou.Ch02.nonnegLaplaceFactorIndepFunAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:04:19.177098+00:00
-- url     : https://prove2.me/theorems/f079c3e5-759c-467d-8471-905be3c01127
-- title:
--   Joint Laplace factorisation implies independence for a.e. measurable nonnegative variables
-- statement:
--   Take nonnegative measurable modifications by max with zero, use the measurable factorisation theorem, and transfer independence back by almost sure equality.
-- source:
--   Kyprianou (2006), Exercise 2.8: Laplace factorisation of positive and negative variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.nonnegLaplaceFactorIndepFunAEV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Ω → ℝ) (hmA : AEMeasurable A P) (hmB : AEMeasurable B P)
    (hnA : ∀ᵐ ω ∂P, 0 ≤ A ω) (hnB : ∀ᵐ ω ∂P, 0 ≤ B ω)
    (h : ∀ u v : ℝ, 0 < u → 0 < v →
      (∫ ω, Real.exp (-(u*A ω+v*B ω)) ∂P) =
      (∫ ω, Real.exp (-(u*A ω)) ∂P)*(∫ ω, Real.exp (-(v*B ω)) ∂P)) :
    IndepFun A B P := by sorry
