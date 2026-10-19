-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_exponentVector_weight
-- name    : OAI.PiExponent.LogarithmicJetIdeals.exponentVector_weight
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T22:00:38.92682+00:00
-- url     : https://prove2.me/theorems/0bc3f3db-e0cd-4ca0-94a9-886adfc13dfa
-- title:
--   Weighted degree is preserved by the exponent vector encoding
-- statement:
--   The exponent vector encoding has the same value at every coordinate as the original function, so any weighted sum over its coordinates is unchanged.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.exponentVector_weight
    {n : ℕ} (q : Fin n → ℝ) (a : Fin n → ℕ) :
    (∑ j, q j * (InterpolationMatrix.exponentVector a j : ℝ)) =
      ∑ j, q j * (a j : ℝ) := by sorry
