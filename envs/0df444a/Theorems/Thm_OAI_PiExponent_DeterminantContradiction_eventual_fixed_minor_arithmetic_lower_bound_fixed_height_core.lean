-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_fixed_minor_arithmetic_lower_bound_fixed_height_core
-- name    : OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_arithmetic_lower_bound_fixed_height_core
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T08:16:25.357055+00:00
-- url     : https://prove2.me/theorems/a930c8be-6bc4-4663-a861-1a1f65f1cda7
-- title:
--   Fixed-height arithmetic lower bound for a nonzero selected minor
-- statement:
--   At each positive fixed height, every selected minor with nonzero determinant satisfies the normalized arithmetic lower bound. This isolates the pointwise arithmetic argument; the parent obtains the eventual result by applying it at positive heights and using the positive slack.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_arithmetic_lower_bound_fixed_height_core
    {nu : Real} (d : FixedData nu) (H : Real) (hH : 0 < H)
    (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    -(1 - actualMean d H) - d.arithmeticError ≤
      Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : Real) * H) := by sorry
