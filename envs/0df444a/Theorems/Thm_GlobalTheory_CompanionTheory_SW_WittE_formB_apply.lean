-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_formB_apply
-- name    : GlobalTheory.CompanionTheory.SW.WittE.formB_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:43.414694+00:00
-- url     : https://prove2.me/theorems/44301230-58f5-420e-95f1-f2f78b5ee682
-- title:
--   Witt E: form B apply
-- statement:
--   The Witt E construction uses the form B apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L253-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L253-L254

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.WittE
variable {E : Type} [Field E]

theorem GlobalTheory.CompanionTheory.SW.WittE.formB_apply (s : E →+* E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    formB s J x y = hform s J x y := by sorry
