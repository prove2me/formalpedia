-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mul_mem_spanA
-- name    : GroundTheory.LocalField.mul_mem_spanA
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:29.486193+00:00
-- url     : https://prove2.me/theorems/c1fbad5e-7deb-43bb-bf58-edcf46e16e05
-- title:
--   Local Field: mul mem span A
-- statement:
--   The Local Field construction uses the mul mem span A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L192-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L192-L201

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

theorem GroundTheory.LocalField.mul_mem_spanA {ζ : ℂ} {f g : G → ℂ} (hf : f ∈ spanA E ζ) (hg : g ∈ spanA E ζ) :
    f * g ∈ spanA E ζ := by sorry
