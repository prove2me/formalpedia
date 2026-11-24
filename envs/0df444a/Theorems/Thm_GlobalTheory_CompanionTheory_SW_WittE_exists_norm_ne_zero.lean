-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_exists_norm_ne_zero
-- name    : GlobalTheory.CompanionTheory.SW.WittE.exists_norm_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:12:52.987072+00:00
-- url     : https://prove2.me/theorems/916a53cd-2a3b-403a-9850-cb5a6df274df
-- title:
--   Witt E: exists norm ne zero
-- statement:
--   The Witt E construction uses the exists norm ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L103-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L103-L121

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
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] {σ : E →+* E}

theorem GlobalTheory.CompanionTheory.SW.WittE.exists_norm_ne_zero (B : V →ₛₗ[σ] V →ₗ[E] E) (hB : ∀ x y, σ (B x y) = B y x)
    (h2 : (2 : E) ≠ 0) {n : ℕ} (X : Fin n → V) (hX : ¬ ∀ a b, B (X a) (X b) = 0) :
    ∃ c : Fin n → E, B (lin X c) (lin X c) ≠ 0 := by sorry
