-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_modCharacter_eq_one
-- name    : GroundTheory.Global.Cyclotomic.modCharacter_eq_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:47.452859+00:00
-- url     : https://prove2.me/theorems/c5e2faed-696c-41af-bf1b-ed8a49039909
-- title:
--   Cyclotomic: mod Character eq one
-- statement:
--   The Cyclotomic construction uses the mod Character eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L129-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L129-L132

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
variable {n : ℕ} [NeZero n]

theorem GroundTheory.Global.Cyclotomic.modCharacter_eq_one {ζ : ℚ̄} (hζ : IsPrimitiveRoot ζ n) {σ : Gal(ℚ̄/ℚ)} (h : σ ζ = ζ) :
    modCharacter n σ = 1 := by sorry
