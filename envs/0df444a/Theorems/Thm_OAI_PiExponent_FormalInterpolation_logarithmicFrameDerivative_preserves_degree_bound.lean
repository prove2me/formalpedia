-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicFrameDerivative_preserves_degree_bound
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicFrameDerivative_preserves_degree_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:49:22.719928+00:00
-- url     : https://prove2.me/theorems/5f95a2db-d1ed-4ddf-97b0-f23390844534
-- title:
--   A logarithmic frame derivative preserves the weighted degree bound
-- statement:
--   For positive weights, applying one logarithmic frame derivative preserves the weighted support bound. At index zero, prove the Euler term preserves monomial weight and each term in the finite sum of partial derivatives lowers it; at other indices, prove the partial derivative lowers it. The monomial cases follow from `pderiv_monomial` and `X_mul_pderiv_monomial`; support bounds for sums combine the component bounds. Positivity is needed for the lowering terms, including when a differentiated monomial becomes zero.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicFrameDerivative_preserves_degree_bound
    {m : Nat} (w : Fin (m + 1) → Rat) (H : Real)
    (hw : ∀ i, 0 < (w i : Real))
    (i : Fin (m + 1))
    (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w H F) :
    logarithmicDegreeBound w H (logarithmicFrameDerivative i F) := by sorry
