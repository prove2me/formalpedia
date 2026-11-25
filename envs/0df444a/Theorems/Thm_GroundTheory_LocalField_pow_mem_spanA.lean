-- Prove2me | Theorems.Thm_GroundTheory_LocalField_pow_mem_spanA
-- name    : GroundTheory.LocalField.pow_mem_spanA
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:14.250799+00:00
-- url     : https://prove2.me/theorems/9c076448-add9-45f8-967d-1addb3a7cc04
-- title:
--   Local Field: pow mem span A
-- statement:
--   The Local Field construction uses the pow mem span A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L203-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L203-L211

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
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
open scoped Classical
variable {G : Type*} [Group G] [Fintype G]
variable {E : Subgroup G → Prop} (hE : ∀ K L : Subgroup G, E K → L ≤ K → E L)
  (hmono : ∀ K : Subgroup G, E K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hE hmono

theorem GroundTheory.LocalField.pow_mem_spanA {ζ : ℂ} {f : G → ℂ} (hf : f ∈ spanA E ζ) {M : ℕ} (hM : M ≠ 0) :
    f ^ M ∈ spanA E ζ := by sorry
