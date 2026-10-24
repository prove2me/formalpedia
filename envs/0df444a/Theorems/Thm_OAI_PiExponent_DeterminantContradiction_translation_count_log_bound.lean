-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_count_log_bound
-- name    : OAI.PiExponent.DeterminantContradiction.translation_count_log_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:29:39.742976+00:00
-- url     : https://prove2.me/theorems/9ae770cb-9872-424e-998a-80f87917a153
-- title:
--   Floor translation count is bounded by the explicit count
-- statement:
--   Compare the floor-based finite translation count with the explicit real-valued count in the target. Positivity of the height and of `d.v0` gives the floor bounds and positive logarithm arguments, including when the exponent is zero.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.translation_count_log_bound {nu : Real} (d : FixedData nu) {H : Real} (hH : 0 < H) :
    Real.log ((((⌊H⌋₊ + 1) ^ (2 * d.m) *
      (⌊H / (d.v0 : Real)⌋₊ + 1) : Nat) : Real)) ≤
      Real.log ((H + 1) ^ (2 * d.m) * (H / (d.v0 : Real) + 1)) := by sorry
