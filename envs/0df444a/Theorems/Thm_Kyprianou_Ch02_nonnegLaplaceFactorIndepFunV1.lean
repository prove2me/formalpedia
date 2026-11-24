-- Prove2me | Theorems.Thm_Kyprianou_Ch02_nonnegLaplaceFactorIndepFunV1
-- name    : Kyprianou.Ch02.nonnegLaplaceFactorIndepFunV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:02:24.374509+00:00
-- url     : https://prove2.me/theorems/40dd21a3-3490-419e-8e36-067d909ddcf7
-- title:
--   Factorisation of joint Laplace transforms implies independence
-- statement:
--   Tilt P by exp(-v B) and use scalar Laplace uniqueness to show the law of A is unchanged. This gives restricted Laplace factors on every upper ray; apply the proved Avram independence criterion.
-- source:
--   Kyprianou (2006), Exercise 2.8, independence of Jordan variation components.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.nonnegLaplaceFactorIndepFunV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Ω → ℝ) (hmA : Measurable A) (hmB : Measurable B)
    (hnA : ∀ ω, 0 ≤ A ω) (hnB : ∀ ω, 0 ≤ B ω)
    (h : ∀ u v : ℝ, 0 < u → 0 < v →
      (∫ ω, Real.exp (-(u*A ω+v*B ω)) ∂P) =
      (∫ ω, Real.exp (-(u*A ω)) ∂P)*(∫ ω, Real.exp (-(v*B ω)) ∂P)) :
    IndepFun A B P := by sorry
