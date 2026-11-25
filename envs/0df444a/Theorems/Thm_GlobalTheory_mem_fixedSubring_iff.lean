-- Prove2me | Theorems.Thm_GlobalTheory_mem_fixedSubring_iff
-- name    : GlobalTheory.mem_fixedSubring_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:29.76469+00:00
-- url     : https://prove2.me/theorems/c0c9f495-d0ab-4c0b-b90b-ca81a3598fa0
-- title:
--   Global Theory: mem fixed Subring iff
-- statement:
--   The Global Theory construction uses the mem fixed Subring iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable (A G : Type*) [CommRing A] [Group G] [MulSemiringAction G A]

theorem GlobalTheory.mem_fixedSubring_iff {a : A} : a ∈ FixedPoints.subring A G ↔ ∀ g : G, g • a = a := by sorry
