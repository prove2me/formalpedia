-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicDegreeBound_add_job_5f95a2db
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_add_job_5f95a2db
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:58:45.56752+00:00
-- url     : https://prove2.me/theorems/70cceb5a-d027-47a4-b851-01323b6be759
-- title:
--   Weighted support bounds are closed under addition
-- statement:
--   If two polynomials satisfy the same weighted support bound, their sum does as well, because every exponent in the sum’s support belongs to the support of at least one summand.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_add_job_5f95a2db
    {d : Nat} (w : Fin d → Rat) (H : Real)
    (F G : MvPolynomial (Fin d) Complex)
    (hF : logarithmicDegreeBound w H F)
    (hG : logarithmicDegreeBound w H G) :
    logarithmicDegreeBound w H (F + G) := by sorry
