-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_word_support_bound
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_word_support_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:44:36.734688+00:00
-- url     : https://prove2.me/theorems/e29411fb-8cda-4849-9768-9a3822f2a1fc
-- title:
--   Derivative words preserve the weighted support cutoff
-- statement:
--   Applying any finite word of partial derivatives does not increase the closed weighted support bound, provided all coordinate weights are nonnegative. This includes the empty word and preserves the equality boundary of the cutoff.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_word_support_bound
    {m : Nat} (W : Fin m → Rat) (N : Nat)
    (F : MvPolynomial (Fin m) Complex)
    (hF : fibreContactSupportBound W N F)
    (word : List (Fin m))
    (hW : ∀ i, 0 ≤ (W i : Real)) :
    fibreContactSupportBound W N (fibreContactWord word F) := by sorry
