-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicDegreeBound_pderiv_job_5f95a2db
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_pderiv_job_5f95a2db
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:57:57.717645+00:00
-- url     : https://prove2.me/theorems/98f85d92-125f-4b3b-95d2-6d6a481c19a2
-- title:
--   A partial derivative preserves a positive weighted support bound
-- statement:
--   For strictly positive weights, a partial derivative preserves the polynomial’s weighted support upper bound: every surviving derivative monomial has one less exponent in the differentiated coordinate, so its weight decreases. If the derivative is zero, the bound holds because its support is empty.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib.Algebra.MvPolynomial.PDeriv

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_pderiv_job_5f95a2db
    {m : Nat} (w : Fin (m + 1) → Rat) (H : Real)
    (hw : ∀ i, 0 < (w i : Real))
    (i : Fin (m + 1))
    (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w H F) :
    logarithmicDegreeBound w H (MvPolynomial.pderiv i F) := by sorry
