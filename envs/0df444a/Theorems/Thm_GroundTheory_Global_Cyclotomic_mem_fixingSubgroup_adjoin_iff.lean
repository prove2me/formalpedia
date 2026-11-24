-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_mem_fixingSubgroup_adjoin_iff
-- name    : GroundTheory.Global.Cyclotomic.mem_fixingSubgroup_adjoin_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:38:08.03174+00:00
-- url     : https://prove2.me/theorems/43b89e7f-b547-41fb-9d14-0428f752255d
-- title:
--   Cyclotomic: mem fixing Subgroup adjoin iff
-- statement:
--   The Cyclotomic construction uses the mem fixing Subgroup adjoin iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L27-L33

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
open scoped Pointwise
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem GroundTheory.Global.Cyclotomic.mem_fixingSubgroup_adjoin_iff (S : Set E) (σ : Gal(E/F)) :
    σ ∈ (adjoin F S).fixingSubgroup ↔ ∀ x ∈ S, σ x = x := by sorry
