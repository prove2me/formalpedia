-- Prove2me | Theorems.Thm_Kyprianou_Ch02_nonnegLaplaceCellIdentityV1
-- name    : Kyprianou.Ch02.nonnegLaplaceCellIdentityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:04:16.447244+00:00
-- url     : https://prove2.me/theorems/bf7e2bf6-446b-494e-b8e9-2281097c1f7a
-- title:
--   Laplace expectations of mutually exclusive cell contributions add after subtracting one
-- statement:
--   Each contribution is nonnegative and at least one is zero. The bounded exponential integrands therefore obey a pointwise additive identity. Integrate it.
-- source:
--   Kyprianou (2006), Exercise 2.8: Laplace factorisation of positive and negative variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.nonnegLaplaceCellIdentityV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hm : AEMeasurable Z P) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    let a := ∫ ω, Real.exp (-(u*max (Z ω) 0)) ∂P
    let b := ∫ ω, Real.exp (-(v*max (-Z ω) 0)) ∂P
    a ∈ Set.Icc 0 1 ∧ b ∈ Set.Icc 0 1 ∧ 0 ≤ a+b-1 ∧
      (∫ ω, Real.exp (-(u*max (Z ω) 0+v*max (-Z ω) 0)) ∂P) = a+b-1 := by sorry
