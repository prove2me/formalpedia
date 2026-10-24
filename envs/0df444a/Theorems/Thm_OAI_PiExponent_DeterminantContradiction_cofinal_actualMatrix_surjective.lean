-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_cofinal_actualMatrix_surjective
-- name    : OAI.PiExponent.DeterminantContradiction.cofinal_actualMatrix_surjective
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T06:02:54.531287+00:00
-- url     : https://prove2.me/theorems/7c0fddd0-0911-490c-9062-aa65243e1bc3
-- title:
--   Cofinal surjectivity of the actual interpolation matrix
-- statement:
--   For every fixed admissible datum and every real lower bound, there is a positive height above that bound at which the actual interpolation matrix is surjective.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.cofinal_actualMatrix_surjective
    (nu : Real) (d : FixedData nu) (L : Real) :
    ∃ H : Real, L ≤ H ∧ 0 < H ∧
      Function.Surjective (actualMatrix d H).mulVecLin := by
  sorry
