-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_polynomialJet_interpolation_of_injective_centers
-- name    : OAI.PiExponent.LogarithmicJetIdeals.polynomialJet_interpolation_of_injective_centers
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T23:01:53.000865+00:00
-- url     : https://prove2.me/theorems/d3134d17-6912-447e-bc29-ad638a5d71c9
-- title:
--   Finite logarithmic staircase interpolation at distinct centers
-- statement:
--   At an injective finite family of centers, arbitrary staircase coefficient packets have a polynomial interpolant without a degree restriction. Distinct centers give comaximal local ideals, so Chinese remainder interpolation applies to their powers. Positivity of e ensures finite packets. For k=0 or K=0 the constraints are empty; when m=0, injectivity permits at most one center.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets

open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.polynomialJet_interpolation_of_injective_centers
    {m K : ℕ} (c : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (he : ∀ i, 0 < e i)
    (hc : Function.Injective c) (k : ℕ)
    (f : Fin K → (Fin (m + 1) →₀ ℕ) → ℂ) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ j : Fin K, ∀ u : Fin (m + 1) →₀ ℕ,
        (∑ i, u i / e i) < k →
          MvPolynomial.coeff u (polynomialJet (c j) T P) = f j u := by sorry
