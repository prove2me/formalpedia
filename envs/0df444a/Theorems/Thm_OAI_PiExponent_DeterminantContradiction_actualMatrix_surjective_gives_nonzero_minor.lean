-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualMatrix_surjective_gives_nonzero_minor
-- name    : OAI.PiExponent.DeterminantContradiction.actualMatrix_surjective_gives_nonzero_minor
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:08:45.714861+00:00
-- url     : https://prove2.me/theorems/030565cf-4544-4b27-ba19-0bdf97a6f1e0
-- title:
--   Extract a nonsingular full-row minor from surjectivity
-- statement:
--   At a fixed height, surjectivity of the exact interpolation matrix yields an injective selection of columns whose square minor on all rows has nonzero determinant. This is the finite-dimensional rank-to-minor step and does not add assumptions on the cutoff or truncation orders.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.actualMatrix_surjective_gives_nonzero_minor
    {nu : Real} (d : FixedData nu) (H : Real)
    (h : Function.Surjective (actualMatrix d H).mulVecLin) :
    ∃ selection : Row d H → Column d H,
      Function.Injective selection ∧ (actualMinor d H selection).det ≠ 0 := by sorry
