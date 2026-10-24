-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_row_count_pos
-- name    : OAI.PiExponent.DeterminantContradiction.actual_row_count_pos
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:58:03.451098+00:00
-- url     : https://prove2.me/theorems/ccd0458a-da7c-426f-963a-8f1f9f1d5bbd
-- title:
--   Positive row count at positive height
-- statement:
--   At positive height the all-zero exponent tuple belongs to the strict weighted simplex. Since the number of row blocks K is positive, the row type is nonempty and its cardinality is positive.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.actual_row_count_pos
    {nu : Real} (d : FixedData nu) (H : Real) (hH : 0 < H) :
    0 < (actualRowCount d H : Real) := by
  sorry
