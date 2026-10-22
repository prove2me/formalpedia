-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicFrameDerivative_zero_preserves_degree
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicFrameDerivative_zero_preserves_degree
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T09:06:46.640278+00:00
-- url     : https://prove2.me/theorems/6e8ca306-6723-48c6-845a-45da476abb1a
-- title:
--   The first logarithmic frame operator preserves weighted support degree
-- statement:
--   For positive rational weights, the index-zero logarithmic frame operator, which combines multiplication of the first partial derivative by the first variable with the sum of the remaining partial derivatives, preserves the weighted support-degree bound.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicFrameDerivative_zero_preserves_degree
    {m : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real))
    (N : Real) (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w N F) :
    logarithmicDegreeBound w N (logarithmicFrameDerivative (0 : Fin (m + 1)) F) := by sorry
