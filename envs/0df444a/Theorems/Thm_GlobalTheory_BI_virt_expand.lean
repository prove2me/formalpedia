-- Prove2me | Theorems.Thm_GlobalTheory_BI_virt_expand
-- name    : GlobalTheory.BI.virt_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:31.735579+00:00
-- url     : https://prove2.me/theorems/863d008e-df6a-4c7a-9b99-603abd285146
-- title:
--   BI: virt expand
-- statement:
--   The BI construction uses the virt expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharacterIrreducibleExpansionNormSq.lean#L67-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharacterIrreducibleExpansionNormSq.lean#L67-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInductionIrreducibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingSelfIrreducibleAlgClosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersIffSubCharactersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_StarVirtualCharacterEqApplyInvStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingEqZeroOfDistinctIrreduStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterIrreducibleExpansionNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.BI
open Polynomial

theorem GlobalTheory.BI.virt_expand : ∀ (G : Type) [Group G] [Finite G]
    (φ : G → ℂ), φ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G →
    ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) ∧
      φ = c.sum (fun χ m => m • χ) ∧
      ∑ᶠ g, φ g * star (φ g) = (c.sum fun _ m => (m : ℂ) ^ 2) * (Nat.card G : ℂ) := by sorry
