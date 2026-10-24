-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicDegreeBound_eulerTerm_job_5f95a2db
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_eulerTerm_job_5f95a2db
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:58:16.57487+00:00
-- url     : https://prove2.me/theorems/1892e072-0a9f-41c2-bfc4-89c92f0df197
-- title:
--   The Euler term preserves weighted support degree
-- statement:
--   Multiplication by `X i` restores the exponent removed by differentiation in coordinate `i`; each surviving monomial therefore has the same weighted degree as its original monomial.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib.Algebra.MvPolynomial.PDeriv

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_eulerTerm_job_5f95a2db
    {m : Nat} (w : Fin (m + 1) → Rat) (H : Real)
    (hw : ∀ i, 0 < (w i : Real))
    (i : Fin (m + 1))
    (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w H F) :
    logarithmicDegreeBound w H
      (MvPolynomial.X i * MvPolynomial.pderiv i F) := by sorry
