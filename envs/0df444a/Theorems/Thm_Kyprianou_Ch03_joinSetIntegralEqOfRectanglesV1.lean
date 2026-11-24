-- Prove2me | Theorems.Thm_Kyprianou_Ch03_joinSetIntegralEqOfRectanglesV1
-- name    : Kyprianou.Ch03.joinSetIntegralEqOfRectanglesV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T12:27:39.889467+00:00
-- url     : https://prove2.me/theorems/47be5c74-dbca-432b-880d-d5c4ac947099
-- title:
--   Equality of integrals on rectangles extends to the joined sigma algebra
-- statement:
--   For two integrable functions, equality of their set integrals on the intersections of measurable sets from two sub-sigma algebras extends to their join by the pi-lambda theorem.
-- source:
--   Dynkin pi-lambda theorem and countable additivity of integrals.

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.joinSetIntegralEqOfRectanglesV1
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) (m h : MeasurableSpace Omega)
    (hjoin : m ⊔ h ≤ mΩ)
    (f z : Omega → ℝ) (hf : Integrable f P) (hz : Integrable z P)
    (hrect : ∀ C D : Set Omega, MeasurableSet[m] C → MeasurableSet[h] D →
      (∫ x in C ∩ D, z x ∂P) = ∫ x in C ∩ D, f x ∂P) :
    ∀ S : Set Omega, MeasurableSet[m ⊔ h] S →
      (∫ x in S, z x ∂P) = ∫ x in S, f x ∂P := by sorry
