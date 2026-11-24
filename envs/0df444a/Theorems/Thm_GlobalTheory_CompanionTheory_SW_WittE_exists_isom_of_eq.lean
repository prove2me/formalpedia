-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_exists_isom_of_eq
-- name    : GlobalTheory.CompanionTheory.SW.WittE.exists_isom_of_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:12:36.8146+00:00
-- url     : https://prove2.me/theorems/1b54de27-c687-42b0-9fb8-d095c50c1efd
-- title:
--   Witt E: exists isom of eq
-- statement:
--   The Witt E construction uses the exists isom of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L49-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L49-L75

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

theorem GlobalTheory.CompanionTheory.SW.WittE.exists_isom_of_eq (B : V →ₛₗ[σ] V →ₗ[E] E) (hσ : ∀ x, σ (σ x) = x)
    (hB : ∀ x y, σ (B x y) = B y x) (h2 : (2 : E) ≠ 0) (x y : V) (hxy : B x x = B y y)
    (hq : B x x ≠ 0) :
    ∃ γ : V →ₗ[E] V, IsIsom B γ ∧ γ x = y ∧ ∀ z, B x z = 0 → B y z = 0 → γ z = z := by sorry
