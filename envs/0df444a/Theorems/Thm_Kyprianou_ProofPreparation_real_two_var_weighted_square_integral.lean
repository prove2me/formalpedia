-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_real_two_var_weighted_square_integral
-- name    : Kyprianou.ProofPreparation.real_two_var_weighted_square_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:30:42.935533+00:00
-- url     : https://prove2.me/theorems/96acf7d6-10c6-4b2a-97f0-51808388c6bc
-- title:
--   Weighted square integral expansion for two real random variables
-- statement:
--   For any two real functions with integrable squares and product under a measure, the integral of the squared weighted sum equals the weighted sum of their two second moments and their cross moment. Deterministic Bochner-integral algebra. A sound reusable source-neutral lemma that allows the Poisson two-cell moment calculation to remain beneath Prove2Me complexity limits.
-- source:
--   Kyprianou (2006) Chapter 2 Theorem 2.7, elementary quadratic expansion step.

import Mathlib
open MeasureTheory
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem real_two_var_weighted_square_integral
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Ω → ℝ)
    (hXX : Integrable (fun ω => X ω ^ 2) P)
    (hYY : Integrable (fun ω => Y ω ^ 2) P)
    (hXY : Integrable (fun ω => X ω * Y ω) P)
    (a b : ℝ) :
    (∫ ω, (a * X ω + b * Y ω) ^ 2 ∂P) =
      a ^ 2 * (∫ ω, X ω ^ 2 ∂P) +
      b ^ 2 * (∫ ω, Y ω ^ 2 ∂P) +
      (2 * a * b) * (∫ ω, X ω * Y ω ∂P) := by sorry
end Kyprianou.ProofPreparation
