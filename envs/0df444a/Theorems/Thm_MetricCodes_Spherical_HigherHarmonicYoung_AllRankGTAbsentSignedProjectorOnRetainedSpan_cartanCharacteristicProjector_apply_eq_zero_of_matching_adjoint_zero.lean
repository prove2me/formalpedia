-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAbsentSignedProjectorOnRetainedSpan_cartanCharacteristicProjector_apply_eq_zero_of_matching_adjoint_zero
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan.cartanCharacteristicProjector_apply_eq_zero_of_matching_adjoint_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:07.830035+00:00
-- url     : https://prove2.me/theorems/6cfb0777-cfb8-43d2-9447-ada194ddd53b
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan.cartanCharacteristicProjector_apply_eq_zero_of_matching_adjoint_zero
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
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 500000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschSpectralProjection
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherChannel

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan.cartanCharacteristicProjector_apply_eq_zero_of_matching_adjoint_zero
    {κ ι V : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (nodes : κ → ℝ) (hnode : Function.Injective nodes)
    (T : Module.End ℝ V) (selected : κ)
    (channelIndex : ι → κ) (hindex : Function.Injective channelIndex)
    (A : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪A i p, A j q⟫_ℝ = 0)
    (heigen : ∀ (i : ι) (p : E i),
      T (A i p) = nodes (channelIndex i) • A i p)
    (x : V)
    (hx : x ∈ (⨆ i : ι, LinearMap.range (A i).toLinearMap))
    (hzero : ∀ i : ι, channelIndex i = selected →
      (A i).toLinearMap.adjoint x = 0) :
    cartanCharacteristicInterpolationProjector nodes T selected x = 0 := by sorry
