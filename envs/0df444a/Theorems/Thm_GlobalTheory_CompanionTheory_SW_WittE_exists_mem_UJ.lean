-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_exists_mem_UJ
-- name    : GlobalTheory.CompanionTheory.SW.WittE.exists_mem_UJ
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:12:55.870124+00:00
-- url     : https://prove2.me/theorems/65f3e718-a429-4b6a-8be9-d9aa2d29a7a1
-- title:
--   Witt E: exists mem UJ
-- statement:
--   The Witt E construction uses the exists mem UJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L268-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L268-L289

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

theorem GlobalTheory.CompanionTheory.SW.WittE.exists_mem_UJ (s : E →+* E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0)
    (γ : (Fin M → E) →ₗ[E] (Fin M → E)) (hγ : IsIsom (formB s J) γ) :
    ∃ g ∈ UJ s J, ∀ z, (g : Matrix (Fin M) (Fin M) E) *ᵥ z = γ z := by sorry
