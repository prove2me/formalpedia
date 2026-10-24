-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_pos_of_height_pos
-- name    : OAI.PiExponent.DeterminantContradiction.actualRowCount_pos_of_height_pos
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T16:56:24.374299+00:00
-- url     : https://prove2.me/theorems/135cdc30-0343-41ac-b9bc-0f761979a83e
-- title:
--   Positive height gives a nonempty row set
-- statement:
--   Positive height makes the actual row set nonempty, so its finite cardinality is positive.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.actualRowCount_pos_of_height_pos
    (nu : Real) (d : FixedData nu) (H : Real) (hH : 0 < H) :
    0 < actualRowCount d H := by sorry
