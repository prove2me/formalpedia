-- Prove2me | Theorems.Thm_GlobalTheory_T_ind_restrict_eq_card_fixedBy_mul_of_classFn
-- name    : GlobalTheory.T.ind_restrict_eq_card_fixedBy_mul_of_classFn
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:46:49.679172+00:00
-- url     : https://prove2.me/theorems/0850cd5f-2ddf-499c-9d05-e9d8b13807b9
-- title:
--   T: ind restrict eq card fixed By mul of class Fn
-- statement:
--   The T construction uses the ind restrict eq card fixed By mul of class Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IndRestrictEqCardFixedByMulStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IndRestrictEqCardFixedByMulStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IndRestrictEqCardFixedByMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IndRestrictEqCardFixedByMulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ind_restrict_eq_card_fixedBy_mul_of_classFn : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (χ : G → L), (∀ g x : G, χ (x⁻¹ * g * x) = χ g) → ∀ g : G, ind H (fun h : H => χ h) g = (Nat.card (MulAction.fixedBy (G ⧸ H) g) : L) * χ g := by sorry
