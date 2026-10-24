-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_candidate_analytic_bound
-- name    : OAI.PiExponent.DeterminantContradiction.actual_minor_candidate_analytic_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T17:54:30.933861+00:00
-- url     : https://prove2.me/theorems/ecc58825-bcde-47b3-b021-cca77ad0d27b
-- title:
--   Uniform analytic bound for selected minors
-- statement:
--   At each positive height, every selected minor with nonzero determinant satisfies the target logarithmic bound using the explicit remainder. The positivity hypothesis is retained for the height-dependent estimates. A proof route expands the determinant over translation choices, bounds each summand and the number of choices, and combines these bounds with the collision contribution.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.actual_minor_candidate_analytic_bound {nu : Real} (d : FixedData nu) {H : Real}
    (hH : 0 < H) (selection : Row d H → Column d H)
    (hne : (actualMinor d H selection).det ≠ 0) :
    Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : Real) * H) ≤
      d.analyticError +
        (Real.log (actualRowCount d H : Real) + Real.log 2 / 4 -
          Real.log (1 - Real.exp (-Real.log 2 / 2)) +
          Real.log ((H + 1) ^ (2 * d.m) * (H / (d.v0 : Real) + 1))) / H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H)) := by sorry
