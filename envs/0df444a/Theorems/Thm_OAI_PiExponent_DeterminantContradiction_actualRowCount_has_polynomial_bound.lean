-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_has_polynomial_bound
-- name    : OAI.PiExponent.DeterminantContradiction.actualRowCount_has_polynomial_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:58:33.52542+00:00
-- url     : https://prove2.me/theorems/abc02e17-6237-4525-9dea-4d8616cecd31
-- title:
--   Polynomial bound for the actual row count
-- statement:
--   For fixed admissible data, eventually the actual row count is positive and bounded above by a constant times (H+1)^(m+1). Each of the m+1 coordinates of the strict weighted simplex has only O(H) possibilities, and the factor K is fixed. The positivity assertion handles the logarithm of the row count; the estimate is also valid in the zero-coordinate boundary case, although admissible data here requires m≥1.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology

theorem OAI.PiExponent.DeterminantContradiction.actualRowCount_has_polynomial_bound {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) : ∃ C : Real, 0 < C ∧ ∀ᶠ H : Real in atTop, 0 < (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) ∧ (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) ≤ C * (H + 1) ^ (d.m + 1) := by sorry
