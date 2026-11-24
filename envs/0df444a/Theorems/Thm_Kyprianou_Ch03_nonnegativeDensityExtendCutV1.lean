-- Prove2me | Theorems.Thm_Kyprianou_Ch03_nonnegativeDensityExtendCutV1
-- name    : Kyprianou.Ch03.nonnegativeDensityExtendCutV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T13:15:13.491531+00:00
-- url     : https://prove2.me/theorems/dfb1ef8b-5ecf-4181-a1b9-8de029bb9f19
-- title:
--   Extend consistent nonnegative densities over increasing measurable cuts
-- statement:
--   Continuity from below and monotone convergence extend finite-cut density equalities to their union; finiteness of Q provides integrability.
-- source:
--   Kyprianou (2006), Corollary 3.11; decomposition of 87ef6563-5569-47b4-b375-99ef3353c600

import Mathlib
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.nonnegativeDensityExtendCutV1
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : ℕ → Set Omega) (Z : Omega → ℝ)
    (hB : ∀ n, MeasurableSet (B n)) (hmono : Monotone B)
    (hZ : ∀ omega, 0 ≤ Z omega)
    (hint : ∀ n, Integrable ((B n).indicator Z) P)
    (heq : ∀ n, Q (B n) = ENNReal.ofReal (∫ omega, (B n).indicator Z omega ∂P)) :
    Q (⋃ n, B n) = ENNReal.ofReal (∫ omega, (⋃ n, B n).indicator Z omega ∂P) := by sorry
