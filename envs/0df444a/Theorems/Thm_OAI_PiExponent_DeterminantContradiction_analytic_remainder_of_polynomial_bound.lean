-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_analytic_remainder_of_polynomial_bound
-- name    : OAI.PiExponent.DeterminantContradiction.analytic_remainder_of_polynomial_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:59:09.130477+00:00
-- url     : https://prove2.me/theorems/8e10e1d3-4902-4251-8b69-a59e6d3fe8e6
-- title:
--   Polynomial row bound implies vanishing analytic remainder
-- statement:
--   Given an eventual positive polynomial upper bound for the row count, the exact logarithmic remainder in the target tends to zero after division by H. Eventually H is positive, the logarithm is monotone on positive arguments, and the numerator is bounded using logarithms of fixed powers of H+1 and H/v0+1. Their growth divided by H tends to zero. This child carries the analytic estimate and the transfer from the row-count bound; it preserves the target's constants and exponents.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology

theorem OAI.PiExponent.DeterminantContradiction.analytic_remainder_of_polynomial_bound {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) (hbound : ∃ C : Real, 0 < C ∧ ∀ᶠ H : Real in atTop, 0 < (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) ∧ (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) ≤ C * (H + 1) ^ (d.m + 1)) : Tendsto (fun H : Real => (Real.log (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) + Real.log 2 / 4 - Real.log (1 - Real.exp (-Real.log 2 / 2)) + Real.log ((H + 1) ^ (2 * d.m) * (H / (d.v0 : Real) + 1))) / H) atTop (𝓝 0) := by sorry
