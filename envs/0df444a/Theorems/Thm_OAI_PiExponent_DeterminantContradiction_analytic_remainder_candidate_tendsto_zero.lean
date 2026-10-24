-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_analytic_remainder_candidate_tendsto_zero
-- name    : OAI.PiExponent.DeterminantContradiction.analytic_remainder_candidate_tendsto_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:54:11.688195+00:00
-- url     : https://prove2.me/theorems/a5e98c68-6293-43a2-8fa1-08a94838436d
-- title:
--   Polynomial-envelope analytic remainder vanishes
-- statement:
--   For fixed admissible data, the explicit logarithmic remainder divided by height tends to zero. This removes the analytic limit obligation from the parent; a proof can bound the row count and the polynomial envelope by powers of height and apply standard logarithm-over-linear-growth limits.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology

theorem OAI.PiExponent.DeterminantContradiction.analytic_remainder_candidate_tendsto_zero {nu : Real} (d : FixedData nu) :
    Tendsto (fun H : Real =>
      (Real.log (actualRowCount d H : Real) + Real.log 2 / 4 -
        Real.log (1 - Real.exp (-Real.log 2 / 2)) +
        Real.log ((H + 1) ^ (2 * d.m) * (H / (d.v0 : Real) + 1))) / H)
      atTop (𝓝 0) := by sorry
