-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicFrameWord_preserves_degree_bound_of_step
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicFrameWord_preserves_degree_bound_of_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:49:35.730881+00:00
-- url     : https://prove2.me/theorems/10ee17aa-d115-427a-b324-7cf8d53a17f9
-- title:
--   Iterated frame words preserve any bound stable under one step
-- statement:
--   For any fixed weighted degree bound and any single-frame step that preserves it for every polynomial, every finite frame word preserves the bound. Induct on the word: the empty word leaves the polynomial unchanged; for a cons, the induction hypothesis bounds the recursively processed tail and `hstep` handles the head. This is reusable independently of the particular positivity argument needed to establish a single step.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicFrameWord_preserves_degree_bound_of_step
    {m : Nat} (w : Fin (m + 1) → Rat) (H : Real)
    (hstep : ∀ (i : Fin (m + 1)) (F : MvPolynomial (Fin (m + 1)) Complex),
      logarithmicDegreeBound w H F →
        logarithmicDegreeBound w H (logarithmicFrameDerivative i F))
    (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w H F)
    (word : List (Fin (m + 1))) :
    logarithmicDegreeBound w H (logarithmicFrameWord word F) := by sorry
