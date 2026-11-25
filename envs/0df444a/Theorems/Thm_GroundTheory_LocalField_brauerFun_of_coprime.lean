-- Prove2me | Theorems.Thm_GroundTheory_LocalField_brauerFun_of_coprime
-- name    : GroundTheory.LocalField.brauerFun_of_coprime
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:35:33.325055+00:00
-- url     : https://prove2.me/theorems/a7e03fef-142a-4c6f-aad4-144d39ea770a
-- title:
--   Local Field: brauer Fun of coprime
-- statement:
--   The Local Field construction uses the brauer Fun of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L378-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L378-L409

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
include hζ hmono
omit hζ hmono

theorem GroundTheory.LocalField.brauerFun_of_coprime {y : G} (hy : (orderOf y).Coprime p) :
    ∃ m : ℕ, brauerFun p y = m ∧ ¬ p ∣ m := by sorry
