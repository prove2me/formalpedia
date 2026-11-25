-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsCharacter_apply_mem_adjoin_card
-- name    : GroundTheory.LocalField.IsCharacter.apply_mem_adjoin_card
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:35:38.677831+00:00
-- url     : https://prove2.me/theorems/56ce9076-349a-44c8-b186-aa8f05413452
-- title:
--   Is Character: apply mem adjoin card
-- statement:
--   The Is Character construction uses the apply mem adjoin card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionIntegral.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionIntegral.lean#L102-L105

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
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
variable {G : Type*} [Group G] [Fintype G]

theorem GroundTheory.LocalField.IsCharacter.apply_mem_adjoin_card {χ : G → ℂ} (hχ : IsCharacter χ) (s : G) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Nat.card G)) : χ s ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by sorry
