-- Prove2me | Theorems.Thm_GlobalTheory_BI_exists_isChar_eq_add_of_injective
-- name    : GlobalTheory.BI.exists_isChar_eq_add_of_injective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:58:08.661056+00:00
-- url     : https://prove2.me/theorems/7c968097-9fe8-467a-9196-b827f6fc2674
-- title:
--   BI: exists is Char eq add of injective
-- statement:
--   The BI construction uses the exists is Char eq add of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsCharacterQuotientOfInjectiveIntertwining.lean#L8-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsCharacterQuotientOfInjectiveIntertwining.lean#L8-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_LinearMapShortExactCommuteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCharacterQuotientOfInjectiveIntertwining
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

theorem GlobalTheory.BI.exists_isChar_eq_add_of_injective : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W) (f : Representation.IntertwiningMap σ ρ), Function.Injective f → ∃ c : G → L, IsChar K L c ∧ ∀ g, algebraMap K L (ρ.character g) = algebraMap K L (σ.character g) + c g := by sorry
