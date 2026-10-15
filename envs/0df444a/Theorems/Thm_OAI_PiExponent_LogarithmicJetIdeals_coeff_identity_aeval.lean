-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_identity_aeval
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coeff_identity_aeval
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T23:14:47.122914+00:00
-- url     : https://prove2.me/theorems/a2363c21-11f8-407d-b074-b6f067dbb3a8
-- title:
--   Identity-variable evaluation preserves polynomial coefficients
-- statement:
--   Evaluating a multivariate polynomial at the corresponding multivariate power-series variables preserves its coefficient at every exponent vector, including the vector obtained from `a` by `InterpolationMatrix.exponentVector`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coeff_identity_aeval
    {m : ℕ} (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (a : Fin (m + 1) → ℕ) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (MvPolynomial.aeval MvPowerSeries.X Q) =
    MvPolynomial.coeff (InterpolationMatrix.exponentVector a) Q := by sorry
