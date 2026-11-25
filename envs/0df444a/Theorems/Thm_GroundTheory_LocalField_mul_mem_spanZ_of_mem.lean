-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mul_mem_spanZ_of_mem
-- name    : GroundTheory.LocalField.mul_mem_spanZ_of_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:33:10.831796+00:00
-- url     : https://prove2.me/theorems/2e0c0a02-262d-49c4-b0d1-10f2db879dce
-- title:
--   Local Field: mul mem span Z of mem
-- statement:
--   The Local Field construction uses the mul mem span Z of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L171-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L171-L179

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

theorem GroundTheory.LocalField.mul_mem_spanZ_of_mem {f g : G → ℂ} (hf : f ∈ spanZ E) (hg : g ∈ spanZ E) :
    f * g ∈ spanZ E := by sorry
