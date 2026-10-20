-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirPureAxis_gtTensorCasimir_tmul_eq_vector_add_young_sub_mixed
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis.gtTensorCasimir_tmul_eq_vector_add_young_sub_mixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:03.313092+00:00
-- url     : https://prove2.me/theorems/f5d50496-7011-4661-9967-aec6d1fd689d
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis.gtTensorCasimir_tmul_eq_vector_add_young_sub_mixed
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
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis.gtTensorCasimir_tmul_eq_vector_add_young_sub_mixed
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) lam) :
    gtTensorCasimir lam (v ⊗ₜ[ℝ] p) =
      (gtEuclideanCasimir n v) ⊗ₜ[ℝ] p +
        v ⊗ₜ[ℝ] (youngAmbientCasimir lam p) -
          gtMixedRotationOperator lam (v ⊗ₜ[ℝ] p) := by sorry
