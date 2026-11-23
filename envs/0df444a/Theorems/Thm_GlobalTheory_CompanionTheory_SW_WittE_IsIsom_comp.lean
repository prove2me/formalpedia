-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_IsIsom_comp
-- name    : GlobalTheory.CompanionTheory.SW.WittE.IsIsom.comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:29.484867+00:00
-- url     : https://prove2.me/theorems/859f1660-d9e9-406d-af89-2d5010de700c
-- title:
--   Is Isom: comp
-- statement:
--   The Is Isom construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L16-L18

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

theorem GlobalTheory.CompanionTheory.SW.WittE.IsIsom.comp {B : V →ₛₗ[σ] V →ₗ[E] E} {γ δ : V →ₗ[E] V} (hγ : IsIsom B γ)
    (hδ : IsIsom B δ) : IsIsom B (γ ∘ₗ δ) := by sorry
