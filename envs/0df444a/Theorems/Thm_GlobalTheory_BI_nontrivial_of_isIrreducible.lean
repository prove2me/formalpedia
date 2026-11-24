-- Prove2me | Theorems.Thm_GlobalTheory_BI_nontrivial_of_isIrreducible
-- name    : GlobalTheory.BI.nontrivial_of_isIrreducible
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:01:29.181958+00:00
-- url     : https://prove2.me/theorems/0b495f56-2125-4767-bbf7-4d494cd27dce
-- title:
--   BI: nontrivial of is Irreducible
-- statement:
--   The BI construction uses the nontrivial of is Irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrreducibleCharacterLinearOrInducedAbelianByPrim.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrreducibleCharacterLinearOrInducedAbelianByPrim.lean#L29-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CommuteImageAbelianByPrimePowerOfNormalCentralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCharacterEigenvectorOfCommutingRepresentatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterEqInducedOfImprimitivitySystemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleIdempotentEqOneAndCharacterEqWeightAlStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsWeightIdempotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleCharacterLinearOrInducedAbelianByPrim
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

theorem GlobalTheory.BI.nontrivial_of_isIrreducible {L G V : Type} [Field L] [Group G] [AddCommGroup V]
    [Module L V] (ρ : Representation L G V) (h : ρ.IsIrreducible) : Nontrivial V := by sorry
