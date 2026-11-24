-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_GaussOrth_measurableEmbedding_mulVec
-- name    : GlobalTheory.CompanionTheory.SW.ThW.GaussOrth.measurableEmbedding_mulVec
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:10:58.766833+00:00
-- url     : https://prove2.me/theorems/b32c8843-3ead-4423-bc28-9422693574c5
-- title:
--   Gauss Orth: measurable Embedding mul Vec
-- statement:
--   The Gauss Orth construction uses the measurable Embedding mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianChangeOfVariablesIsometry.lean#L44-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianChangeOfVariablesIsometry.lean#L44-L65

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianChangeOfVariablesIsometry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW GlobalTheory.CompanionTheory.SW.ThW.GaussOrth
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem GlobalTheory.CompanionTheory.SW.ThW.GaussOrth.measurableEmbedding_mulVec {W ι : Type} [Fintype W] [Fintype ι] [DecidableEq ι]
    {g : W → Matrix ι ι ℝ} (h : ∀ w, (g w).det ≠ 0) :
    MeasurableEmbedding (fun (x : W → ι → ℝ) (w : W) => g w *ᵥ x w) := by sorry
