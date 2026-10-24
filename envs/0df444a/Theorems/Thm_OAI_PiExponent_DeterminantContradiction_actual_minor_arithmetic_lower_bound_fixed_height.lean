-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_arithmetic_lower_bound_fixed_height
-- name    : OAI.PiExponent.DeterminantContradiction.actual_minor_arithmetic_lower_bound_fixed_height
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T06:37:21.473439+00:00
-- url     : https://prove2.me/theorems/39e8d45a-49b7-4fed-9fbf-3bb9fc6b0719
-- title:
--   Fixed-height arithmetic lower bound for a nonzero selected minor
-- statement:
--   At every positive fixed height, each selection whose minor determinant is nonzero satisfies the normalized arithmetic lower bound. This child contains the fixed-height arithmetic argument; the parent obtains the eventual estimate by applying it for positive heights and subtracting the positive slack.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.actual_minor_arithmetic_lower_bound_fixed_height
    {nu : Real} (d : FixedData nu) (H : Real) (hH : 0 < H)
    (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    -(1 - actualMean d H) - d.arithmeticError ≤
      Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : Real) * H) := by sorry
