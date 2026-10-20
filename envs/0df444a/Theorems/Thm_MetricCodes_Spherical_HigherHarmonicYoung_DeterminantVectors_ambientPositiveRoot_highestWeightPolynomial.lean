-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_DeterminantVectors_ambientPositiveRoot_highestWeightPolynomial
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors.ambientPositiveRoot_highestWeightPolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:54.32227+00:00
-- url     : https://prove2.me/theorems/77647e45-6ad3-4073-bb2a-1ca0fdb4fa11
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors.ambientPositiveRoot_highestWeightPolynomial
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors

theorem MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors.ambientPositiveRoot_highestWeightPolynomial {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (e : Fin (r + 1) → ℕ)
    (p q : Fin (r + 1)) (hpq : p < q) :
    ambientPositiveRoot h p q (highestWeightPolynomial h e) = 0 := by sorry
