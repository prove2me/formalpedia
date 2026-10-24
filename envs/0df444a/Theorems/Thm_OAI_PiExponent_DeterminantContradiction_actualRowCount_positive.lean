-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_positive
-- name    : OAI.PiExponent.DeterminantContradiction.actualRowCount_positive
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T18:03:48.067779+00:00
-- url     : https://prove2.me/theorems/f0926770-0a38-4949-838f-c3b19a757806
-- title:
--   Positivity of the actual row count for positive H
-- statement:
--   For fixed admissible data and H>0, the actual row count is positive.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology

theorem OAI.PiExponent.DeterminantContradiction.actualRowCount_positive {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) {H : Real} (hH : 0 < H) : 0 < (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) := by sorry
