-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_character_eq_one_iff
-- name    : GroundTheory.Global.Cyclotomic.character_eq_one_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:23.609793+00:00
-- url     : https://prove2.me/theorems/18b6c92f-3fbc-4083-b2e3-614b95078ee2
-- title:
--   Cyclotomic: character eq one iff
-- statement:
--   The Cyclotomic construction uses the character eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L239-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L239-L250

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

theorem GroundTheory.Global.Cyclotomic.character_eq_one_iff (σ : Gal(ℚ̄/ℚ)) :
    character σ = 1 ↔ ∀ x : ℚ̄, (∃ n : ℕ, 0 < n ∧ x ^ n = 1) → σ x = x := by sorry
