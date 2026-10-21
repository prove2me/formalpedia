-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_power_membership_iff_polynomialJet_coefficients
-- name    : OAI.PiExponent.LogarithmicJetIdeals.power_membership_iff_polynomialJet_coefficients
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T21:58:00.053319+00:00
-- url     : https://prove2.me/theorems/c21c2cc7-780e-43ff-9636-44c0f05157d5
-- title:
--   Ideal-power membership through polynomial logarithmic jet coefficients
-- statement:
--   For positive coordinate exponents and distinct arithmetic-progression centers, membership in a power of the simultaneous jet ideal is equivalent to vanishing of the translated polynomial jet coefficients on the staircase defined by the sum of coordinatewise integer quotients being strictly less than the power index.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets

open OAI.PiExponent OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.power_membership_iff_polynomialJet_coefficients
    {m : ℕ} (K : ℕ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ)
    (hr : ∃ i, r i ≠ 0) (he : ∀ i, 0 < e i)
    (k : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ) :
    P ∈ (simultaneousJetIdeal K r T e) ^ k ↔
      ∀ j : Fin K, ∀ u : Fin (m + 1) →₀ ℕ,
        (∑ i, u i / e i) < k →
          MvPolynomial.coeff u
            (polynomialJet (fun i => (j.val : ℂ) * r i) T P) = 0 := by sorry
