-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_exists_isom_tuple
-- name    : GlobalTheory.CompanionTheory.SW.WittE.exists_isom_tuple
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:12:47.112893+00:00
-- url     : https://prove2.me/theorems/7ddff797-8b23-4d75-8714-ca1772e21d7b
-- title:
--   Witt E: exists isom tuple
-- statement:
--   The Witt E construction uses the exists isom tuple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L130-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L130-L232

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
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  {σ : E →+* E}

theorem GlobalTheory.CompanionTheory.SW.WittE.exists_isom_tuple (B : V →ₛₗ[σ] V →ₗ[E] E) (hσ : ∀ x, σ (σ x) = x)
    (hB : ∀ x y, σ (B x y) = B y x) (h2 : (2 : E) ≠ 0) {n : ℕ} (k : ℕ) :
    ∀ X Y : Fin n → V, Module.finrank E (Submodule.span E (Set.range X)) = k →
      (∀ a b, B (X a) (X b) = B (Y a) (Y b)) →
      (∀ c : Fin n → E, (∀ a, B (X a) (lin X c) = 0) → lin X c = 0 ∧ lin Y c = 0) →
      ∃ γ : V →ₗ[E] V, IsIsom B γ ∧ ∀ a, γ (X a) = Y a := by sorry
