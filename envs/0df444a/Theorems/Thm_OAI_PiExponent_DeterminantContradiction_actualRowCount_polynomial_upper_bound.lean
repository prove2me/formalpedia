-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_polynomial_upper_bound
-- name    : OAI.PiExponent.DeterminantContradiction.actualRowCount_polynomial_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:03:32.275963+00:00
-- url     : https://prove2.me/theorems/1baf7115-4f5d-404b-8daf-d44b70984a6f
-- title:
--   Polynomial upper bound for the actual row count
-- statement:
--   For fixed admissible data, the actual row count is bounded by a fixed positive constant times (H+1)^(m+1) for every H≥1.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology

theorem OAI.PiExponent.DeterminantContradiction.actualRowCount_polynomial_upper_bound {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) : ∃ C : Real, 0 < C ∧ ∀ H : Real, 1 ≤ H → (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) ≤ C * (H + 1) ^ (d.m + 1) := by sorry
