-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicDegreeBound_add_support_v2
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_add_support_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T09:27:44.682883+00:00
-- url     : https://prove2.me/theorems/9a473ff0-c4cb-4917-bc95-16a1e69ee5ac
-- title:
--   Weighted bound is closed under addition
-- statement:
--   Addition preserves a common weighted support-degree bound because the support of a sum is contained in the union of the supports. A proof route uses support membership for addition; cancellation only removes terms.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_add_support_v2
    {d : Nat} (w : Fin d → Rat) (N : Real)
    (F G : MvPolynomial (Fin d) Complex)
    (hF : logarithmicDegreeBound w N F)
    (hG : logarithmicDegreeBound w N G) :
    logarithmicDegreeBound w N (F + G) := by sorry
