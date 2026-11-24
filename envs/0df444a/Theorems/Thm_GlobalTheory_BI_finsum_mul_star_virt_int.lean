-- Prove2me | Theorems.Thm_GlobalTheory_BI_finsum_mul_star_virt_int
-- name    : GlobalTheory.BI.finsum_mul_star_virt_int
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:59:10.291742+00:00
-- url     : https://prove2.me/theorems/cc8567fd-91be-4bff-8d96-5f69c835768f
-- title:
--   BI: finsum mul star virt int
-- statement:
--   The BI construction uses the finsum mul star virt int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharacterInnerEqIntMulCard.lean#L23-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharacterInnerEqIntMulCard.lean#L23-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingAddNatPosSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersIffSubCharacters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_StarVirtualCharacterEqApplyInvStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterInnerEqIntMulCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
open Polynomial

theorem GlobalTheory.BI.finsum_mul_star_virt_int : ∀ (G : Type) [Group G] [Finite G] (a b : G → ℂ),
    a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G → b ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G →
    ∃ m : ℤ, ∑ᶠ g, a g * star (b g) = m * (Nat.card G : ℂ) := by sorry
