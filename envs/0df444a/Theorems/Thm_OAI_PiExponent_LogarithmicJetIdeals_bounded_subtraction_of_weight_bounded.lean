-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_bounded_subtraction_of_weight_bounded
-- name    : OAI.PiExponent.LogarithmicJetIdeals.bounded_subtraction_of_weight_bounded
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T23:08:09.281328+00:00
-- url     : https://prove2.me/theorems/a6490e09-fac9-4216-a454-a29dc0194168
-- title:
--   Bounded support gives a monic pure leading term
-- statement:
--   For a polynomial whose support exponents all satisfy the given weight cutoff, subtract it from the pure monomial at exponent N i. The result has leading coefficient one and degree exactly that pure exponent, including when the exponent is zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Complex.Basic

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.bounded_subtraction_of_weight_bounded (m : ℕ) (w : Fin (m + 1) → ℝ) (D : ℝ) (N : Fin (m + 1) → ℕ) (o : MonomialOrder (Fin (m + 1))) (hN : ∀ i, D < (N i : ℝ) * w i) (ho : ∀ i b, (∑ j, w j * (b j : ℝ) ≤ D) → o.toSyn b < o.toSyn (Finsupp.single i (N i))) (i : Fin (m + 1)) (Q : MvPolynomial (Fin (m + 1)) ℂ) (hQ : ∀ b ∈ Q.support, ∑ j, w j * (b j : ℝ) ≤ D) : (o.leadingCoeff (MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ) - Q) = 1) ∧ (o.degree (MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ) - Q) = Finsupp.single i (N i)) := by sorry
