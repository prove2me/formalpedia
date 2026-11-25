-- Prove2me | Theorems.Thm_GroundTheory_LocalField_not_dvd_brauerFun
-- name    : GroundTheory.LocalField.not_dvd_brauerFun
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:49.449873+00:00
-- url     : https://prove2.me/theorems/fcd3ca45-5873-4d54-84f0-153070a76851
-- title:
--   Local Field: not dvd brauer Fun
-- statement:
--   The Local Field construction uses the not dvd brauer Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L411-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L411-L420

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

theorem GroundTheory.LocalField.not_dvd_brauerFun (s : G) : ∃ k : ℤ, brauerFun p s = k ∧ ¬ (p : ℤ) ∣ k := by sorry
