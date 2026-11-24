-- Prove2me | Theorems.Thm_GlobalTheory_BI_isChar_of_isChar_of_mem_virt
-- name    : GlobalTheory.BI.isChar_of_isChar_of_mem_virt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:01:01.918743+00:00
-- url     : https://prove2.me/theorems/357a9f49-dcd5-48e4-a07f-d006003a1600
-- title:
--   BI: is Char of is Char of mem virt
-- statement:
--   The BI construction uses the is Char of is Char of mem virt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldOfVirtualAndCharacter.lean#L17-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldOfVirtualAndCharacter.lean#L17-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterExtendScalarsRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIsCharEqAddOfPairNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInductionIrreducibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingAddNatPosSymmStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersIffSubCharactersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfVirtualAndCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI

theorem GlobalTheory.BI.isChar_of_isChar_of_mem_virt (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L]
    (G : Type) [Group G] [Finite G] (χ : G → L) (hχ : _root_.GlobalTheory.BI.IsChar L L χ) (hv : χ ∈ _root_.GlobalTheory.BI.Virt K L G) :
    _root_.GlobalTheory.BI.IsChar K L χ := by sorry
