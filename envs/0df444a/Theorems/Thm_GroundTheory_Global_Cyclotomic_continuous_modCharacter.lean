-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_continuous_modCharacter
-- name    : GroundTheory.Global.Cyclotomic.continuous_modCharacter
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:20.26357+00:00
-- url     : https://prove2.me/theorems/92c5583d-3109-4415-8ce2-8a1083dac41a
-- title:
--   Cyclotomic: continuous mod Character
-- statement:
--   The Cyclotomic construction uses the continuous mod Character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L134-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Character.lean#L134-L149

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

theorem GroundTheory.Global.Cyclotomic.continuous_modCharacter (n : ℕ) [NeZero n] :
    Continuous fun σ : Gal(ℚ̄/ℚ) => (modCharacter n σ : ZMod n) := by sorry
