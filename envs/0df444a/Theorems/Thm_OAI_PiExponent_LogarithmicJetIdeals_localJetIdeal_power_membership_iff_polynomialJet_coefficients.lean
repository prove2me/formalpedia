-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_localJetIdeal_power_membership_iff_polynomialJet_coefficients
-- name    : OAI.PiExponent.LogarithmicJetIdeals.localJetIdeal_power_membership_iff_polynomialJet_coefficients
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T22:07:14.260145+00:00
-- url     : https://prove2.me/theorems/14651708-7a91-424e-bfe9-2e9e8227c6e7
-- title:
--   Local jet ideal powers through polynomial jet coefficients
-- statement:
--   For positive coordinate exponents, membership in a power of one local jet ideal is equivalent to the vanishing of the polynomial jet coefficients on the corresponding quotient staircase.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets

open OAI.PiExponent OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.localJetIdeal_power_membership_iff_polynomialJet_coefficients
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (he : ∀ i, 0 < e i)
    (k : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ) :
    P ∈ (localJetIdeal c T e) ^ k ↔
      ∀ u : Fin (m + 1) →₀ ℕ,
        (∑ i, u i / e i) < k →
          MvPolynomial.coeff u (polynomialJet c T P) = 0 := by sorry
