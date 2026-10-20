-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalSelectedTwoBlockClosure_gtPhysicalTensor_mem_submodule_of_full_axis_transverse_projection
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalSelectedTwoBlockClosure.gtPhysicalTensor_mem_submodule_of_full_axis_transverse_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:15.843669+00:00
-- url     : https://prove2.me/theorems/cbd0c3f2-13fa-4237-95b9-a5d787f00700
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalSelectedTwoBlockClosure.gtPhysicalTensor_mem_submodule_of_full_axis_transverse_projection
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
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalSelectedTwoBlockClosure
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalCompleteBlockReconstruction
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalSelectedTwoBlockClosure.gtPhysicalTensor_mem_submodule_of_full_axis_transverse_projection
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1) (hdom : Antitone lam)
    (S : Submodule ℝ
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (x : SpherePacking.Euclidean (n + 1) ⊗[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (haxis : ∀ mu : FullBranchWeight lam,
      gtFullAxisEmbedding lam hn mu
        ((gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint x) ∈ S)
    (htransverse : ∀ mu : FullBranchWeight lam,
      gtFullTransverseEmbedding lam hn mu
        ((gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint x) ∈ S) :
    x ∈ S := by sorry
