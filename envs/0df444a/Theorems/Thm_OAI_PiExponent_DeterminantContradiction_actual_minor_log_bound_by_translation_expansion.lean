-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_log_bound_by_translation_expansion
-- name    : OAI.PiExponent.DeterminantContradiction.actual_minor_log_bound_by_translation_expansion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T18:29:22.156782+00:00
-- url     : https://prove2.me/theorems/aa96e798-55ad-4887-9437-d7c96aeef9d2
-- title:
--   Selected-minor logarithmic estimate with translation remainder
-- statement:
--   Bound the normalized logarithm of each nonzero selected minor by the analytic term, the explicit collision contribution, the logarithm of the floor-based translation count, and the target maximum term. This isolates the determinant expansion and translated-summand estimates; porting those estimates from the pinned analytic source is the main remaining proof work.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.actual_minor_log_bound_by_translation_expansion {nu : Real} (d : FixedData nu) (hnu : 0 ≤ nu) {H : Real} (hH : 0 < H) (selection : Row d H → Column d H) (hne : (actualMinor d H selection).det ≠ 0) :
    Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : Real) * H) ≤
      d.analyticError +
        (Real.log (actualRowCount d H : Real) + Real.log 2 / 4 -
          Real.log (1 - Real.exp (-Real.log 2 / 2))) / H +
        Real.log ((((⌊H⌋₊ + 1) ^ (2 * d.m) *
          (⌊H / (d.v0 : Real)⌋₊ + 1) : Nat) : Real)) / H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H)) := by sorry
