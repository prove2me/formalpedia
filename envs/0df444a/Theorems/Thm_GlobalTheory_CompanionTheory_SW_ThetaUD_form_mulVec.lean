-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThetaUD_form_mulVec
-- name    : GlobalTheory.CompanionTheory.SW.ThetaUD.form_mulVec
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:11:13.960565+00:00
-- url     : https://prove2.me/theorems/b6fd2279-97ec-41bc-961e-a496f3c7fd3a
-- title:
--   Theta UD: form mul Vec
-- statement:
--   The Theta UD construction uses the form mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ThetaFunctionModularity.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ThetaFunctionModularity.lean#L10-L13

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ThetaFunctionModularity
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThetaUD
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.ThetaUD.form_mulVec {R ι : Type} [CommRing R] [Fintype ι] (G Q : Matrix ι ι R) (h : Gᵀ * Q * G = Q)
    (v : ι → R) : (G *ᵥ v) ⬝ᵥ (Q *ᵥ (G *ᵥ v)) = v ⬝ᵥ (Q *ᵥ v) := by sorry
