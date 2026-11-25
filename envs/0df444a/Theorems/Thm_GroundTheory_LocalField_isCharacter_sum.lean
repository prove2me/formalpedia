-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isCharacter_sum
-- name    : GroundTheory.LocalField.isCharacter_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:45:00.19951+00:00
-- url     : https://prove2.me/theorems/ddf4ae13-70f6-4ed4-b89e-c95c7100306f
-- title:
--   Local Field: is Character sum
-- statement:
--   The Local Field construction uses the is Character sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L475-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L475-L482

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G : Type*} [Group G]

theorem GroundTheory.LocalField.isCharacter_sum {ι : Type*} (s : Finset ι) {χ : ι → G → ℂ} (h : ∀ i ∈ s, IsCharacter (χ i)) :
    IsCharacter (∑ i ∈ s, χ i) := by sorry
