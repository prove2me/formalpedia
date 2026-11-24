-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableSecondMomentVarianceV1
-- name    : Kyprianou.Ch03.stableSecondMomentVarianceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T19:17:21.608827+00:00
-- url     : https://prove2.me/theorems/a739a09c-35f2-4e9d-8e44-d1a3e6c69085
-- title:
--   Second moment inequality and equality at unit moments
-- statement:
--   Integrate the nonnegative square of Z minus its mean. When both moments are one, the square of Z minus one has zero integral and therefore vanishes almost surely.
-- source:
--   Auxiliary second-moment inequality for Kyprianou (2006), Exercise 3.7.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.stableSecondMomentVarianceV1
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Omega → ℝ) (hi : Integrable Z P) (hi2 : Integrable (fun w => Z w ^ 2) P) :
    (∫ w, Z w ∂P)^2 ≤ ∫ w, Z w^2 ∂P ∧
      ((∫ w, Z w ∂P) = 1 → (∫ w, Z w^2 ∂P) = 1 → Z =ᵐ[P] 1) := by sorry
