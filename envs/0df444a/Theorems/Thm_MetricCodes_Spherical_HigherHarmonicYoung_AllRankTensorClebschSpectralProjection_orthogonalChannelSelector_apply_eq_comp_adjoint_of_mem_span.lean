-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankTensorClebschSpectralProjection_orthogonalChannelSelector_apply_eq_comp_adjoint_of_mem_span
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschSpectralProjection.orthogonalChannelSelector_apply_eq_comp_adjoint_of_mem_span
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:07.830035+00:00
-- url     : https://prove2.me/theorems/37fcd365-f558-4dc6-b7ad-c11700b80432
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschSpectralProjection.orthogonalChannelSelector_apply_eq_comp_adjoint_of_mem_span
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

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschSpectralProjection.orthogonalChannelSelector_apply_eq_comp_adjoint_of_mem_span
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (A : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪A i p, A j q⟫_ℝ = 0)
    (P : Module.End ℝ V) (selected : ι)
    (hselector : ∀ (j : ι) (p : E j),
      P (A j p) = if selected = j then A j p else 0)
    (x : V)
    (hx : x ∈ (⨆ j : ι, LinearMap.range (A j).toLinearMap)) :
    P x =
      ((A selected).toLinearMap.comp
        (A selected).toLinearMap.adjoint) x := by sorry
