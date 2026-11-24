-- Prove2me | Theorems.Thm_GlobalTheory_BI_finsupp_eq_single_of_sum_sq_eq_one
-- name    : GlobalTheory.BI.finsupp_eq_single_of_sum_sq_eq_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:59:59.86801+00:00
-- url     : https://prove2.me/theorems/eadd308f-1aec-4dbb-946b-2642eecec2ce
-- title:
--   BI: finsupp eq single of sum sq eq one
-- statement:
--   The BI construction uses the finsupp eq single of sum sq eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrreducibleOfVirtualCharacterNormOne.lean#L10-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrreducibleOfVirtualCharacterNormOne.lean#L10-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterIrreducibleExpansionNormSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleOfVirtualCharacterNormOne
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

theorem GlobalTheory.BI.finsupp_eq_single_of_sum_sq_eq_one {α : Type} (c : α →₀ ℤ)
    (h : (c.sum fun _ m => m ^ 2) = 1) :
    ∃ a, c.support = {a} ∧ (c a = 1 ∨ c a = -1) := by sorry
