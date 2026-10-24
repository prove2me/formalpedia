-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_log_weighted_polynomial_factor_div_tends_zero
-- name    : OAI.PiExponent.DeterminantContradiction.log_weighted_polynomial_factor_div_tends_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:04:34.976877+00:00
-- url     : https://prove2.me/theorems/6deb280c-57d4-486b-8847-79efa7418114
-- title:
--   Logarithm of the weighted polynomial factor is sublinear
-- statement:
--   For fixed natural m and positive v, the logarithm of `(H+1)^(2*m) * (H/v+1)`, divided by H, tends to zero.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology

theorem OAI.PiExponent.DeterminantContradiction.log_weighted_polynomial_factor_div_tends_zero (m : Nat) (v : Real) (hv : 0 < v) : Tendsto (fun H : Real => Real.log ((H + 1) ^ (2 * m) * (H / v + 1)) / H) atTop (𝓝 0) := by sorry
