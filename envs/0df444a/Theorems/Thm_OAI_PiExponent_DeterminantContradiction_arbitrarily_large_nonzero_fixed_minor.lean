-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_arbitrarily_large_nonzero_fixed_minor
-- name    : OAI.PiExponent.DeterminantContradiction.arbitrarily_large_nonzero_fixed_minor
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T19:17:50.067459+00:00
-- url     : https://prove2.me/theorems/a3234490-3866-481f-b7a4-9b00d39c7160
-- title:
--   Nonzero fixed interpolation minors at arbitrarily large heights
-- statement:
--   Every admissible fixed datum has a nonempty interpolation row set and a nonzero selected square minor at arbitrarily large positive heights.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.arbitrarily_large_nonzero_fixed_minor
    (nu : Real) (d : FixedData nu) (L : Real) :
    ∃ H : Real, L ≤ H ∧ 0 < H ∧ 0 < actualRowCount d H ∧
      ∃ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 := by sorry
