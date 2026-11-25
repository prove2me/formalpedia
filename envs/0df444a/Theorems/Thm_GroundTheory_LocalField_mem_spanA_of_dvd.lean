-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_spanA_of_dvd
-- name    : GroundTheory.LocalField.mem_spanA_of_dvd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:36.365488+00:00
-- url     : https://prove2.me/theorems/52cc40eb-78dc-47f8-8ecd-3773e95a6989
-- title:
--   Local Field: mem span A of dvd
-- statement:
--   The Local Field construction uses the mem span A of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionLocal.lean#L105-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionLocal.lean#L105-L122

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
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
universe u
variable {G : Type u} [Group G] [Fintype G]
variable {E : Subgroup G → Prop} (hE : ∀ K L : Subgroup G, E K → L ≤ K → E L)
  (hmono : ∀ K : Subgroup G, E K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
  (hcyc : ∀ s : G, E (Subgroup.zpowers s))
  {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
include hE hmono hcyc hζ

theorem GroundTheory.LocalField.mem_spanA_of_dvd {F : G → ℂ} (hF : IsClassFun F)
    (hdiv : ∀ g, ∃ k : ℤ, F g = (Nat.card G : ℂ) * k) : F ∈ spanA E ζ := by sorry
