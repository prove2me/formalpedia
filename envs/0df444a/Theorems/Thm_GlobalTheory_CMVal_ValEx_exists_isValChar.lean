-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_exists_isValChar
-- name    : GlobalTheory.CMVal.ValEx.exists_isValChar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:08.72885+00:00
-- url     : https://prove2.me/theorems/c495dcba-88bb-4fa5-8687-4fbd0afb9ccf
-- title:
--   Val Ex: exists is Val Char
-- statement:
--   The Val Ex construction uses the exists is Val Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L430-L562
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L430-L562

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.ValEx.exists_isValChar (E : Type) [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (_hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (v : HeightOneSpectrum (OF E)) (hv : IsBaseCond (v.asIdeal ^ 2)) :
    ∃ χ : HChar E, IsValChar φ s κ (v.asIdeal ^ 2) ∅ χ := by sorry
