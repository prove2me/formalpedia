-- Prove2me | Theorems.Thm_GroundTheory_LocalField_indFun_theta_mem_spanA
-- name    : GroundTheory.LocalField.indFun_theta_mem_spanA
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:19:55.854573+00:00
-- url     : https://prove2.me/theorems/5f2f707b-c283-5755-8492-c044f3eb191a
-- title:
--   Local Field: ind Fun theta mem span A
-- statement:
--   The Local Field construction uses the ind Fun theta mem span A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L242-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L242-L275

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
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
variable {G : Type u} [Group G]
variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)
variable {p x}
variable {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
  (hmono : ∀ K : Subgroup G, IsElementaryAt p K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
omit hp
include hζ hmono

theorem GroundTheory.LocalField.indFun_theta_mem_spanA (hx : (orderOf x).Coprime p) :
    indFun (elemSub p x).subtype (theta p x) ∈ spanA (G := G) (IsElementaryAt p) ζ := by sorry
