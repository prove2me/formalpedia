-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankTensorClebschSpectralProjection_cartanCharacteristicProjector_eq_channel_comp_adjoint_of_complete
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschSpectralProjection.cartanCharacteristicProjector_eq_channel_comp_adjoint_of_complete
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:07.830035+00:00
-- url     : https://prove2.me/theorems/19657633-4fae-4548-97f5-7826d20a3799
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschSpectralProjection.cartanCharacteristicProjector_eq_channel_comp_adjoint_of_complete
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
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschSpectralProjection
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschSpectralProjection.cartanCharacteristicProjector_eq_channel_comp_adjoint_of_complete
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (nodes : ι → ℝ) (hnode : Function.Injective nodes)
    (T : Module.End ℝ V)
    (A : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪A i p, A j q⟫_ℝ = 0)
    (hcomplete : (⨆ i : ι, LinearMap.range (A i).toLinearMap) = ⊤)
    (heigen : ∀ (i : ι) (p : E i), T (A i p) = nodes i • A i p)
    (selected : ι) :
    cartanCharacteristicInterpolationProjector nodes T selected =
      (A selected).toLinearMap.comp (A selected).toLinearMap.adjoint := by sorry
