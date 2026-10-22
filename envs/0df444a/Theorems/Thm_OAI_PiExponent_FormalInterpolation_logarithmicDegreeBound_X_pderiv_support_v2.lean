-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicDegreeBound_X_pderiv_support_v2
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_X_pderiv_support_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T09:27:10.2469+00:00
-- url     : https://prove2.me/theorems/c7e15e8c-6a85-409a-b3c5-53c740a88772
-- title:
--   Weighted bound for a coordinate Euler term
-- statement:
--   Multiplication of a partial derivative by its own variable preserves the weighted support-degree bound. For a supported derivative monomial, multiplication restores the differentiated exponent; vanishing terms and cancellation cannot add support. A proof route is to use the monomial formula for `pderiv` and support membership for multiplication.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_X_pderiv_support_v2
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (N : Real) (F : MvPolynomial (Fin d) Complex)
    (hF : logarithmicDegreeBound w N F) (i : Fin d) :
    logarithmicDegreeBound w N
      (MvPolynomial.X i * MvPolynomial.pderiv i F) := by sorry
