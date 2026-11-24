-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Mobius_det_emb
-- name    : GlobalTheory.CompanionTheory.SW.Core.Mobius.det_emb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:04:00.479808+00:00
-- url     : https://prove2.me/theorems/04ca0f97-25be-4615-871f-b80f7a46392e
-- title:
--   Mobius: det emb
-- statement:
--   The Mobius construction uses the det emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MobiusActionUpperHalfPlane.lean#L55-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MobiusActionUpperHalfPlane.lean#L55-L60

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MobiusActionUpperHalfPlane
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Mobius
variable {F : Type} [Field F]

theorem GlobalTheory.CompanionTheory.SW.Core.Mobius.det_emb (σ : F →+* ℝ) (γ : SL(2, F)) :
    σ (γ 0 0) * σ (γ 1 1) - σ (γ 0 1) * σ (γ 1 0) = 1 := by sorry
