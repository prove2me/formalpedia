-- Prove2me | Theorems.Thm_Kyprianou_Ch01_positiveIntegral_of_ae_pos
-- name    : Kyprianou.Ch01.positiveIntegral_of_ae_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T11:27:56.69209+00:00
-- url     : https://prove2.me/theorems/ccf81867-fbe0-4451-905e-bffcba08c65f
-- title:
--   An integrable almost-everywhere positive real function has strictly positive expectation
-- statement:
--   Under a probability measure, any real-valued integrable function that is strictly positive almost surely has strictly positive integral, using the positive-support criterion.
-- source:
--   General measure-theoretic lemma supporting Kyprianou (2006) Chapter 1 Exercise 1.9(i)

import Mathlib
open MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.positiveIntegral_of_ae_pos
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hi : Integrable f P)
    (hp : ∀ᵐ ω ∂P, 0 < f ω) :
    0 < ∫ ω, f ω ∂P := by sorry
