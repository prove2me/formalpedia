-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsCharacter_exists_sum_zpow
-- name    : GroundTheory.LocalField.IsCharacter.exists_sum_zpow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:01.963409+00:00
-- url     : https://prove2.me/theorems/ae6e32be-8111-47c6-a998-8c4c774fa4ab
-- title:
--   Is Character: exists sum zpow
-- statement:
--   The Is Character construction uses the exists sum zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionIntegral.lean#L56-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionIntegral.lean#L56-L82

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

theorem GroundTheory.LocalField.IsCharacter.exists_sum_zpow {χ : G → ℂ} (hχ : IsCharacter χ) (s : G) :
    ∃ (m : (Subgroup.zpowers s → ℂ) → ℕ) (β : (Subgroup.zpowers s → ℂ) → ℂ),
      (∀ ψ, β ψ ^ orderOf s = 1) ∧
        ∀ a : ℤ, χ (s ^ a) = ∑ ψ ∈ irrChars (Subgroup.zpowers s), (m ψ : ℂ) * β ψ ^ a := by sorry
