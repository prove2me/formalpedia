-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_PoiLat_quad_mulVec
-- name    : GlobalTheory.CompanionTheory.SW.Core.PoiLat.quad_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:37.975791+00:00
-- url     : https://prove2.me/theorems/6b294a54-3897-4aec-a416-dea2e2f99ee1
-- title:
--   Poi Lat: quad mul Vec
-- statement:
--   The Poi Lat construction uses the quad mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PoissonSummationGaussian.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PoissonSummationGaussian.lean#L14-L19

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PoissonSummationGaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.PoiLat
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem GlobalTheory.CompanionTheory.SW.Core.PoiLat.quad_mulVec (P : Matrix κ κ ℝ) (W : Matrix κ κ ℂ) (v : κ → ℝ) :
    (fun i => (((P *ᵥ v) i : ℝ) : ℂ)) ⬝ᵥ (W *ᵥ fun i => (((P *ᵥ v) i : ℝ) : ℂ)) =
      (fun i => (v i : ℂ)) ⬝ᵥ
        (((P.map Complex.ofReal)ᵀ * W * P.map Complex.ofReal) *ᵥ fun i => (v i : ℂ)) := by sorry
