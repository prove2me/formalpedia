-- Prove2me | Theorems.Thm_GlobalTheory_BI_isChar_finsum_conj_ext0_of_isChar
-- name    : GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:58:32.906979+00:00
-- url     : https://prove2.me/theorems/57fea7c7-434e-4386-8665-4fc1fcfb1ecd
-- title:
--   BI: is Char finsum conj ext0 of is Char
-- statement:
--   The BI construction uses the is Char finsum conj ext0 of is Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterFinsumConjSubgroupFunctionExtendByZer.lean#L81-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterFinsumConjSubgroupFunctionExtendByZer.lean#L81-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterFinsumConjSubgroupFunctionExtendByZer
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

theorem GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), IsChar K L ψ → IsChar K L (fun g : G => ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) := by sorry
