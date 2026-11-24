-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableNonnegativeOfBoundedNegExpV1
-- name    : Kyprianou.Ch03.stableNonnegativeOfBoundedNegExpV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T19:00:20.544799+00:00
-- url     : https://prove2.me/theorems/29bc45ba-b2cb-4881-a087-67864fa5c962
-- title:
--   Bounded negative exponential moments force nonnegative support
-- statement:
--   If a negative level has positive probability, the exponential moment grows without bound along integer parameters.
-- source:
--   Kyprianou (2006), Exercise 3.7; exact auxiliary for stable regime proofs.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.stableNonnegativeOfBoundedNegExpV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P] (Y : Omega → ℝ)
    (hY : AEMeasurable Y P)
    (hi : ∀ n : ℕ, Integrable (fun w => Real.exp (-(n : ℝ) * Y w)) P)
    (hb : ∀ n : ℕ, (∫ w, Real.exp (-(n : ℝ) * Y w) ∂P) ≤ 1) :
    ∀ᵐ w ∂P, 0 ≤ Y w := by sorry
