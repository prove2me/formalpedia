-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableLogLaplaceCoefficientStrictSignV1
-- name    : Kyprianou.Ch03.stableLogLaplaceCoefficientStrictSignV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:00:20.836472+00:00
-- url     : https://prove2.me/theorems/8ec8f378-7e2c-4096-b641-5c8b95fad99b
-- title:
--   Strict sign of a homogeneous log Laplace transform
-- statement:
--   Apply the nonnegative variance inequality to exp(-Y). The log transform comparison at 1 and 2 determines the sign; zero coefficient would imply exp(-Y)=1 almost surely.
-- source:
--   Kyprianou (2006), Exercise 3.7; exact auxiliary for stable regime proofs.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.stableLogLaplaceCoefficientStrictSignV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P] (Y : Omega → ℝ)
    (alpha : ℝ) (ha : 0 < alpha) (hne : ¬ Y =ᵐ[P] 0)
    (hi : ∀ theta : ℝ, 0 ≤ theta → Integrable (fun w => Real.exp (-theta * Y w)) P)
    (hh : ∀ theta : ℝ, 0 ≤ theta →
      Real.log (∫ w, Real.exp (-theta * Y w) ∂P) =
        Real.log (∫ w, Real.exp (-Y w) ∂P) * theta ^ alpha) :
    (alpha < 1 → Real.log (∫ w, Real.exp (-Y w) ∂P) < 0) ∧
    (1 < alpha → 0 < Real.log (∫ w, Real.exp (-Y w) ∂P)) := by sorry
