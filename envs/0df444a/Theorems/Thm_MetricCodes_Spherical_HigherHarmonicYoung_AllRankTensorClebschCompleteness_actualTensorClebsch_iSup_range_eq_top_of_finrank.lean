-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankTensorClebschCompleteness_actualTensorClebsch_iSup_range_eq_top_of_finrank
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness.actualTensorClebsch_iSup_range_eq_top_of_finrank
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:06.385168+00:00
-- url     : https://prove2.me/theorems/27197551-82c2-4faf-b009-ae006302646c
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness.actualTensorClebsch_iSup_range_eq_top_of_finrank
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
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 500000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness.actualTensorClebsch_iSup_range_eq_top_of_finrank
    {ι : Type*} [Fintype ι]
    {r n : ℕ} (hn : 2 * r + 2 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target)
    (source : ι → Fin (r + 1) → ℕ)
    (hsource : ∀ i, IsAllRankOneBoxNeighbor target (source i))
    (hinj : Function.Injective source)
    (A : (i : ι) → HarmonicYoungSpace (n := n) (source i) →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target))
    (hA : ∀ (i : ι) (a b : Fin n),
      (A i).toLinearMap.comp (youngAmbientRotation (source i) a b) =
        (ClebschRotation.tensorAmbientRotation target a b).comp
          (A i).toLinearMap)
    (hdim : n * Module.finrank ℝ (HarmonicYoungSpace (n := n) target) =
      ∑ i : ι, Module.finrank ℝ
        (HarmonicYoungSpace (n := n) (source i))) :
    (⨆ i : ι, LinearMap.range (A i).toLinearMap) =
      (⊤ : Submodule ℝ
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n) target)) := by sorry
