-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCanonicalSelectedBranchRange_orthogonalBranch_range_eq_of_cross_orthogonal
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange.orthogonalBranch_range_eq_of_cross_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:03.313092+00:00
-- url     : https://prove2.me/theorems/cedd1def-d5c9-4e05-b3ba-ee5b44decbf6
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange.orthogonalBranch_range_eq_of_cross_orthogonal
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
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGTFullCrossOrthogonality
open MetricCodes.Spherical.ThreeRowYoungBranching
variable {ι : Type*} [Fintype ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange.orthogonalBranch_range_eq_of_cross_orthogonal
    (f : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪f i p, f j q⟫_ℝ = 0)
    (hdim : Module.finrank ℝ V =
      ∑ i : ι, Module.finrank ℝ (E i))
    (g : F →ₗᵢ[ℝ] V) (i : ι)
    (hcross : ∀ j : ι, j ≠ i →
      ∀ p : F, ∀ q : E j, ⟪g p, f j q⟫_ℝ = 0)
    (heqdim : Module.finrank ℝ F = Module.finrank ℝ (E i)) :
    LinearMap.range g.toLinearMap =
      LinearMap.range (f i).toLinearMap := by sorry
