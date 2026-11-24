-- Prove2me | Theorems.Thm_GlobalTheory_BI_ind_restrict_eq_card_fixedBy_mul
-- name    : GlobalTheory.BI.ind_restrict_eq_card_fixedBy_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:58:26.429184+00:00
-- url     : https://prove2.me/theorems/58918690-4233-4517-988f-20028ec0ddb5
-- title:
--   BI: ind restrict eq card fixed By mul
-- statement:
--   The BI construction uses the ind restrict eq card fixed By mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IndRestrictEqCardFixedByMul.lean#L14-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IndRestrictEqCardFixedByMul.lean#L14-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InducedClassFunctionFromSubgroupEqFinsumCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IndRestrictEqCardFixedByMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.BI

theorem GlobalTheory.BI.ind_restrict_eq_card_fixedBy_mul : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (χ : G → L), (∀ g x : G, χ (x⁻¹ * g * x) = χ g) → ∀ g : G, ind H (fun h : H => χ h) g = (Nat.card (MulAction.fixedBy (G ⧸ H) g) : L) * χ g := by sorry
