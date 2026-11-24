-- Prove2me | Theorems.Thm_GroundTheory_LocalField_sum_mul_irr_apply
-- name    : GroundTheory.LocalField.sum_mul_irr_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:57.757994+00:00
-- url     : https://prove2.me/theorems/e21a70dc-d370-4b45-992c-fc317f6c79f7
-- title:
--   Local Field: sum mul irr apply
-- statement:
--   The Local Field construction uses the sum mul irr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L363-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L363-L401

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
variable {G : Type*} [Group G] [Fintype G]

theorem GroundTheory.LocalField.sum_mul_irr_apply {f : G → ℂ} (hf : IsClassFun f) {ψ : G → ℂ} (hψ : IsIrrCharacter ψ)
    (h : G) :
    ∑ g, f g * ψ (g⁻¹ * h) = (Nat.card G : ℂ) * charInner G f ψ / ψ 1 * ψ h := by sorry
