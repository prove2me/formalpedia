-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungMixedGapAxisProbability_normalizedChannelIsometry_adjoint_apply
-- name    : MetricCodes.Spherical.HigherYoungMixedGapAxisProbability.normalizedChannelIsometry_adjoint_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:56.928481+00:00
-- url     : https://prove2.me/theorems/7692b969-4a08-48ee-a40c-42aa256f051d
-- title:
--   MetricCodes.Spherical.HigherYoungMixedGapAxisProbability.normalizedChannelIsometry_adjoint_apply
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
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherYoungMixedGapAxisProbability
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherChannel

theorem MetricCodes.Spherical.HigherYoungMixedGapAxisProbability.normalizedChannelIsometry_adjoint_apply
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) (c : ℝ) (hc : 0 < c)
    (h : ∀ p q : E, ⟪A p, A q⟫_ℝ = c * ⟪p, q⟫_ℝ)
    (y : F) :
    (SpherePacking.HarmonicCoordinateOperators.normalizedChannelIsometry
      A c hc h).adjoint y =
        (Real.sqrt c)⁻¹ • A.adjoint y := by sorry
