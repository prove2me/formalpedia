-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_form_lin_right
-- name    : GlobalTheory.CompanionTheory.SW.WittE.form_lin_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:24.259716+00:00
-- url     : https://prove2.me/theorems/a2548d78-da32-4e18-ae06-2072ded43e6c
-- title:
--   Witt E: form lin right
-- statement:
--   The Witt E construction uses the form lin right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L83-L85

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

theorem GlobalTheory.CompanionTheory.SW.WittE.form_lin_right (B : V →ₛₗ[σ] V →ₗ[E] E) {n : ℕ} (X : Fin n → V) (c : Fin n → E) (z : V) :
    B z (lin X c) = ∑ a, c a * B z (X a) := by sorry
