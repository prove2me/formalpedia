-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_surjective_actualMatrix_has_nonzero_minor
-- name    : OAI.PiExponent.DeterminantContradiction.surjective_actualMatrix_has_nonzero_minor
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:03:09.726029+00:00
-- url     : https://prove2.me/theorems/4d388e69-0fbe-44b8-a57e-defb52231309
-- title:
--   Surjectivity yields a nonzero selected minor
-- statement:
--   At a positive height where the actual matrix is surjective, its row type is nonempty and some selection of columns gives a square minor with nonzero determinant.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.surjective_actualMatrix_has_nonzero_minor
    (nu : Real) (d : FixedData nu) (H : Real) (hH : 0 < H)
    (hsurj : Function.Surjective (actualMatrix d H).mulVecLin) :
    0 < actualRowCount d H ∧
      ∃ selection : Row d H → Column d H, (actualMinor d H selection).det ≠ 0 := by
  sorry
