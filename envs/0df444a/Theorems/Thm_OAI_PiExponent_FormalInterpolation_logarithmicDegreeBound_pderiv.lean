-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicDegreeBound_pderiv
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_pderiv
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T09:06:31.943513+00:00
-- url     : https://prove2.me/theorems/a563ae2f-a697-4331-8600-f059650498fa
-- title:
--   A weighted partial derivative preserves support degree
-- statement:
--   For positive rational coordinate weights, an ordinary partial derivative of a polynomial cannot increase its weighted support degree. Its proof reduces to checking that each surviving monomial has its differentiated exponent lowered by one in the selected coordinate; zero derivatives satisfy the bound vacuously.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_pderiv
    {m : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real))
    (N : Real) (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w N F)
    (k : Fin (m + 1)) :
    logarithmicDegreeBound w N (MvPolynomial.pderiv k F) := by sorry
