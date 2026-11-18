-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_real_finset_weighted_square_integral
-- name    : Kyprianou.ProofPreparation.real_finset_weighted_square_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:34:55.568783+00:00
-- url     : https://prove2.me/theorems/705d81fe-331a-418f-9fdb-fbf5c43432a7
-- title:
--   Finite weighted-square integral as a double sum of pairwise moments
-- statement:
--   For a finite family of real random variables with integrable pairwise products, the squared weighted sum has expectation equal to the double weighted sum of expected products. Pure deterministic Bochner-integral algebra proved using finite double-sum expansion, integrable_finset_sum, integral_finset_sum and scalar linearity. This is the abstract quadratic step toward a finite-simple Poisson stochastic integral L² isometry.
-- source:
--   Kyprianou (2006) Chapter 2 Theorem 2.7, finite simple-function quadratic expansion.

import Mathlib
open MeasureTheory
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem real_finset_weighted_square_integral
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (F : Finset ι) (X : ι → Ω → ℝ)
    (a : ι → ℝ)
    (hprod : ∀ i ∈ F, ∀ j ∈ F,
      Integrable (fun ω => X i ω * X j ω) P) :
    (∫ ω, (∑ i ∈ F, a i * X i ω) ^ 2 ∂P) =
      ∑ i ∈ F, ∑ j ∈ F, (a i * a j) *
        (∫ ω, X i ω * X j ω ∂P) := by sorry
end Kyprianou.ProofPreparation
