-- Prove2me | Theorems.Thm_GlobalTheory_T_commute_image_abelianByPrimePower_of_normal_central
-- name    : GlobalTheory.T.commute_image_abelianByPrimePower_of_normal_central
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:29:29.211811+00:00
-- url     : https://prove2.me/theorems/c13cc470-ef09-44e5-b1c8-6e25723dbd9a
-- title:
--   T: commute image abelian By Prime Power of normal central
-- statement:
--   The T construction uses the commute image abelian By Prime Power of normal central property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CommuteImageAbelianByPrimePowerOfNormalCentralStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CommuteImageAbelianByPrimePowerOfNormalCentralStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CommuteImageAbelianByPrimePowerOfNormalCentral
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CommuteImageAbelianByPrimePowerOfNormalCentralStatement
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

theorem GlobalTheory.T.commute_image_abelianByPrimePower_of_normal_central : ∀ (G : Type) [Group G] [Finite G] (M : Type) [Monoid M] (φ : G →* M), AbByP G → (∀ B : Subgroup G, B.Normal → (∀ a ∈ B, ∀ b ∈ B, φ a * φ b = φ b * φ a) → ∀ b ∈ B, ∀ g : G, φ b * φ g = φ g * φ b) → ∀ a b : G, φ a * φ b = φ b * φ a := by sorry
