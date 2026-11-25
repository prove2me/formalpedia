-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mul_mem_spanZ
-- name    : GroundTheory.LocalField.mul_mem_spanZ
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:55:14.08881+00:00
-- url     : https://prove2.me/theorems/5c8ee440-667f-562f-b8dd-92cab4dd6a61
-- title:
--   Local Field: mul mem span Z
-- statement:
--   The Local Field construction uses the mul mem span Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L160-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L160-L169

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

theorem GroundTheory.LocalField.mul_mem_spanZ {χ : G → ℂ} (hχ : IsCharacter χ) {f : G → ℂ} (hf : f ∈ spanZ E) :
    χ * f ∈ spanZ E := by sorry
