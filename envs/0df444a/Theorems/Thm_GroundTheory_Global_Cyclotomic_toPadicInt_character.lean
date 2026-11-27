-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_toPadicInt_character
-- name    : GroundTheory.Global.Cyclotomic.toPadicInt_character
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:34.218562+00:00
-- url     : https://prove2.me/theorems/4c8a65c2-874c-48ed-990e-36e85bc98b05
-- title:
--   Cyclotomic: to Padic Int character
-- statement:
--   The Cyclotomic construction uses the to Padic Int character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L311-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L311-L316

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
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem GroundTheory.Global.Cyclotomic.toPadicInt_character (σ : Gal(ℚ̄/ℚ)) :
    toPadicInt ℓ (character σ : ℤ̂) =
      (cyclotomicCharacter ℚ̄ ℓ (MulSemiringAction.toRingAut Gal(ℚ̄/ℚ) ℚ̄ σ) : ℤ_[ℓ]) := by sorry
