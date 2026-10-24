-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventually_actualMatrix_surjective
-- name    : OAI.PiExponent.DeterminantContradiction.eventually_actualMatrix_surjective
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T06:42:43.511066+00:00
-- url     : https://prove2.me/theorems/783f0ef1-2f32-4819-b455-a1a7c302db9d
-- title:
--   Eventual surjectivity of the truncated interpolation matrix
-- statement:
--   For fixed admissible data, the finite truncated-log interpolation matrix maps column coefficient vectors onto all row data at every sufficiently large real height.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.eventually_actualMatrix_surjective
    (nu : Real) (d : FixedData nu) :
    ∀ᶠ H : Real in atTop,
      Function.Surjective (actualMatrix d H).mulVecLin := by sorry
