-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_smul_one_mem_spanZ
-- name    : GroundTheory.LocalField.exists_smul_one_mem_spanZ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:30:38.053104+00:00
-- url     : https://prove2.me/theorems/7db89a0d-edec-592d-8611-440c23d3833b
-- title:
--   Local Field: exists smul one mem span Z
-- statement:
--   The Local Field construction uses the exists smul one mem span Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L422-L487
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L422-L487

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

theorem GroundTheory.LocalField.exists_smul_one_mem_spanZ :
    ∃ m : ℕ, ¬ p ∣ m ∧ ((m : ℤ) • (1 : G → ℂ)) ∈ spanZ (IsElementaryAt p) := by sorry
