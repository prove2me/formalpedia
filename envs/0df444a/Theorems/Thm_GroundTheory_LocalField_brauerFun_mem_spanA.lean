-- Prove2me | Theorems.Thm_GroundTheory_LocalField_brauerFun_mem_spanA
-- name    : GroundTheory.LocalField.brauerFun_mem_spanA
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:27:00.624009+00:00
-- url     : https://prove2.me/theorems/5e3c6a14-b866-5835-b05d-06d55c22caaa
-- title:
--   Local Field: brauer Fun mem span A
-- statement:
--   The Local Field construction uses the brauer Fun mem span A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L356-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L356-L360

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
omit hp

theorem GroundTheory.LocalField.brauerFun_mem_spanA : brauerFun p ∈ spanA (G := G) (IsElementaryAt p) ζ := by sorry
