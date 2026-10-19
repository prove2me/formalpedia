-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_pure_leading_powers_of_bounded_representatives
-- name    : OAI.PiExponent.LogarithmicJetIdeals.pure_leading_powers_of_bounded_representatives
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:51:45.043418+00:00
-- url     : https://prove2.me/theorems/cafdfd9a-79cb-4c97-acf1-d459ee36323d
-- title:
--   Bounded quotient representatives yield monic pure leading powers
-- statement:
--   For positive variable weights, representatives of weight at most D≥0 give, for one common monomial order, monic pure-leading-power relations in the ideal with each pure-power weight at most D plus that variable’s weight. This generic rounding and monomial-order lemma applies independently of logarithmic jets.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Complex.Basic

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.pure_leading_powers_of_bounded_representatives
    (m : ℕ) (w : Fin (m + 1) → ℝ) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (D : ℝ) (hD : 0 ≤ D)
    (hrep : ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∃ Q : MvPolynomial (Fin (m + 1)) ℂ,
        P - Q ∈ I ∧
        ∀ b ∈ Q.support, ∑ i, w i * (b i : ℝ) ≤ D) :
    ∃ (N : Fin (m + 1) → ℕ)
      (o : MonomialOrder (Fin (m + 1)))
      (f : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ),
      (∀ i, 0 < N i) ∧
      (∀ i, f i ∈ I) ∧
      (∀ i, o.leadingCoeff (f i) = 1) ∧
      (∀ i, o.degree (f i) = Finsupp.single i (N i)) ∧
      (∀ i, (N i : ℝ) * w i ≤ D + w i) := by sorry
