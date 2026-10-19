-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_polynomialJet_aeval_jetCoordinate
-- name    : OAI.PiExponent.LogarithmicJetIdeals.polynomialJet_aeval_jetCoordinate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T17:21:31.963479+00:00
-- url     : https://prove2.me/theorems/165d123e-d18f-4996-82ca-e5acfb73b7dc
-- title:
--   Explicit polynomial inverse for logarithmic jet substitution
-- statement:
--   Substitution by the existing jet coordinates is a right inverse to polynomialJet. Prove this by computing the image of each coordinate and applying multivariate polynomial evaluation composition. It supplies arbitrary polynomial residues at one center and holds for every truncation, including zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets

open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.polynomialJet_aeval_jetCoordinate
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (Q : MvPolynomial (Fin (m + 1)) ℂ) :
    polynomialJet c T (MvPolynomial.aeval (jetCoordinate c T) Q) = Q := by sorry
