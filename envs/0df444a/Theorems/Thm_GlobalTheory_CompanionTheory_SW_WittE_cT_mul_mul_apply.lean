-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_cT_mul_mul_apply
-- name    : GlobalTheory.CompanionTheory.SW.WittE.cT_mul_mul_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:12:23.385742+00:00
-- url     : https://prove2.me/theorems/35f5c9c1-b012-483a-a1ad-3307aadc859e
-- title:
--   Witt E: c T mul mul apply
-- statement:
--   The Witt E construction uses the c T mul mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L263-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L263-L266

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

theorem GlobalTheory.CompanionTheory.SW.WittE.cT_mul_mul_apply (s : E →+* E) {M : ℕ} (J g : Matrix (Fin M) (Fin M) E) (i j : Fin M) :
    (cT s g * J * g) i j = hform s J (fun k => g k i) (fun k => g k j) := by sorry
