-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_coordinate_inverse_identity
-- name    : OAI.PiExponent.LogarithmicJetIdeals.local_coordinate_inverse_identity
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T18:20:08.081849+00:00
-- url     : https://prove2.me/theorems/7a4ccaf8-d152-4a03-9e35-f323eb9baff3
-- title:
--   Local coordinate substitution is inverted by jet coordinates
-- statement:
--   Evaluating a polynomial after the local coordinate substitution at the jet coordinate polynomials recovers the original polynomial. The first coordinate undoes the shift, and in each remaining coordinate the truncated-log terms cancel.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.local_coordinate_inverse_identity
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPolynomial.aeval (jetCoordinate c T) (localCoordinatePolynomial c T P) = P := by sorry
