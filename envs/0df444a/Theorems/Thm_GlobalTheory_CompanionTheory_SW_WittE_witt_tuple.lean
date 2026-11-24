-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_witt_tuple
-- name    : GlobalTheory.CompanionTheory.SW.WittE.witt_tuple
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:13:10.327076+00:00
-- url     : https://prove2.me/theorems/6b4b9dca-a747-4c07-8590-cdba8d760a3a
-- title:
--   Witt E: witt tuple
-- statement:
--   The Witt E construction uses the witt tuple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L293-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L293-L323

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

theorem GlobalTheory.CompanionTheory.SW.WittE.witt_tuple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X Y : Fin n → Fin M → E), gramE σ J X = gramE σ J Y → (gramE σ J X).det ≠ 0 → ∃ g ∈ UJ (σ : E →+* E) J, ∀ a, (g : Matrix (Fin M) (Fin M) E) *ᵥ X a = Y a := by sorry
