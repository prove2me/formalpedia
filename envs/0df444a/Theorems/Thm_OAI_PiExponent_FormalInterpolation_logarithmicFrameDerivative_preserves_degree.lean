-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicFrameDerivative_preserves_degree
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicFrameDerivative_preserves_degree
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T08:58:52.926569+00:00
-- url     : https://prove2.me/theorems/d490403c-8556-47b8-9bae-b7bcb0baec0b
-- title:
--   A logarithmic frame derivative preserves weighted support degree
-- statement:
--   For positive rational weights, applying any one logarithmic frame derivative preserves a polynomial's weighted support-degree bound. The derivative terms reduce exponents, and the distinguished variable-times-derivative term preserves the weighted exponent sum.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicFrameDerivative_preserves_degree
    {m : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real))
    (N : Real) (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w N F)
    (i : Fin (m + 1)) :
    logarithmicDegreeBound w N (logarithmicFrameDerivative i F) := by sorry
