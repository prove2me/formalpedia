-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContactSupportBound_pderiv
-- name    : OAI.PiExponent.FormalInterpolation.fibreContactSupportBound_pderiv
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:29:21.501986+00:00
-- url     : https://prove2.me/theorems/2c365bb2-195a-4b2f-9d21-b3a9962d3d7d
-- title:
--   A partial derivative preserves the weighted support cutoff
-- statement:
--   For nonnegative coordinate weights, one partial derivative preserves the closed weighted support cutoff. This is the only substantive step: each surviving derivative coefficient comes from an original coefficient whose exponent is one larger in the differentiated coordinate.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContactSupportBound_pderiv
    {m : Nat} (W : Fin m → Rat) (N : Nat)
    (F : MvPolynomial (Fin m) Complex)
    (hF : fibreContactSupportBound W N F)
    (i : Fin m)
    (hW : ∀ j, 0 ≤ (W j : Real)) :
    fibreContactSupportBound W N (MvPolynomial.pderiv i F) := by sorry
