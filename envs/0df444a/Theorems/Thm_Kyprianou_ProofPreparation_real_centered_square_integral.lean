-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_real_centered_square_integral
-- name    : Kyprianou.ProofPreparation.real_centered_square_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T13:11:21.61494+00:00
-- url     : https://prove2.me/theorems/6695210b-2805-4050-a975-56ea0425a723
-- title:
--   Integral of squared centred real integrable random variable
-- statement:
--   For a real random variable with integrable first and second powers on a probability space, the expected squared deviation from any constant c equals its second moment minus twice c times its mean plus c squared. This is a deterministic expectation algebra lemma, used to obtain centred Poisson finite simple-function L² isometry from accepted first and second moments.
-- source:
--   Kyprianou (2006) Chapter 2 Theorem 2.7, variance-centering algebra.

import Mathlib
open MeasureTheory
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem real_centered_square_integral
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (J : Ω → ℝ) (c : ℝ)
    (hJ : Integrable J P)
    (hJ2 : Integrable (fun ω => J ω ^ 2) P) :
    (∫ ω, (J ω - c) ^ 2 ∂P) =
      (∫ ω, J ω ^ 2 ∂P) -
        (2 * c) * (∫ ω, J ω ∂P) + c ^ 2 := by sorry
end Kyprianou.ProofPreparation
