-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicDegreeBound_pderiv_support_v2
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_pderiv_support_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T09:27:28.079077+00:00
-- url     : https://prove2.me/theorems/a3ed35c3-2449-44ba-986c-7731e5ad464d
-- title:
--   Weighted bound for a partial derivative
-- statement:
--   A partial derivative in a positive-weight coordinate preserves the upper bound on weighted support degree. A proof route identifies each supported derivative exponent with an original exponent having positive coordinate `i`, then uses positivity of `w i` to bound the reduced degree. Zero derivatives are covered by empty support.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_pderiv_support_v2
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (N : Real) (F : MvPolynomial (Fin d) Complex)
    (hF : logarithmicDegreeBound w N F) (i : Fin d) :
    logarithmicDegreeBound w N (MvPolynomial.pderiv i F) := by sorry
