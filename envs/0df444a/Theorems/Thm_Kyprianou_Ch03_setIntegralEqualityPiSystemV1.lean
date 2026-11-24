-- Prove2me | Theorems.Thm_Kyprianou_Ch03_setIntegralEqualityPiSystemV1
-- name    : Kyprianou.Ch03.setIntegralEqualityPiSystemV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:34:47.640747+00:00
-- url     : https://prove2.me/theorems/0dc84a20-146a-4778-b135-a0755de45083
-- title:
--   Integrable functions with equal integrals on a generating pi-system
-- statement:
--   Equal integrals of integrable real functions on a generating pi-system and the full space extend to its generated sigma algebra by the Dynkin-system argument.
-- source:
--   Exercise 3.1, conditional-expectation rectangle and monotone-class argument for leaf 6a870581-0ee4-4990-b7cb-eb140983d7c6

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.setIntegralEqualityPiSystemV1
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) (j : MeasurableSpace Omega) (hj : j ≤ mΩ)
    (R : Set (Set Omega)) (hgen : j = MeasurableSpace.generateFrom R) (hpi : IsPiSystem R)
    (f q : Omega → ℝ) (hf : Integrable f P) (hq : Integrable q P)
    (htotal : (∫ x, q x ∂P) = ∫ x, f x ∂P)
    (hR : ∀ S ∈ R, (∫ x in S, q x ∂P) = ∫ x in S, f x ∂P) :
    ∀ S : Set Omega, MeasurableSet[j] S → (∫ x in S, q x ∂P) = ∫ x in S, f x ∂P := by sorry
