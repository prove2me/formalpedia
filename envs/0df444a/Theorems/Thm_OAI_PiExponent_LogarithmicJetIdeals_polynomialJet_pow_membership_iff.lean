-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_polynomialJet_pow_membership_iff
-- name    : OAI.PiExponent.LogarithmicJetIdeals.polynomialJet_pow_membership_iff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T23:01:13.37907+00:00
-- url     : https://prove2.me/theorems/9d71acc0-2198-41db-8c29-1709458576cd
-- title:
--   Logarithmic ideal powers detect staircase coefficient vanishing
-- statement:
--   A polynomial lies in the kth power of the local logarithmic coordinate ideal exactly when its polynomial jet has zero coefficients throughout the strict floor-division staircase. The substitution is triangular and invertible for every truncation T. Positive e makes the monomial criterion valid; k=0 gives the whole ring and an empty coefficient condition.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets

open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.polynomialJet_pow_membership_iff
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (he : ∀ i, 0 < e i)
    (k : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ) :
    P ∈ localJetIdeal c T e ^ k ↔
      ∀ u : Fin (m + 1) →₀ ℕ, (∑ i, u i / e i) < k →
        MvPolynomial.coeff u (polynomialJet c T P) = 0 := by sorry
