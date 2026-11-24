-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_formB_conj
-- name    : GlobalTheory.CompanionTheory.SW.WittE.formB_conj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:12:58.238588+00:00
-- url     : https://prove2.me/theorems/7a48fa89-8f80-4fcb-ac5c-4c364da13be1
-- title:
--   Witt E: form B conj
-- statement:
--   The Witt E construction uses the form B conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L256-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L256-L261

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

theorem GlobalTheory.CompanionTheory.SW.WittE.formB_conj (s : E →+* E) (hs : ∀ x, s (s x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, s (J j i) = J i j) (x y : Fin M → E) :
    s (formB s J x y) = formB s J y x := by sorry
