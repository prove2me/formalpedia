-- Prove2me | Theorems.Thm_GlobalTheory_injective_baseChange_invariants_subtype
-- name    : GlobalTheory.injective_baseChange_invariants_subtype
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:41.927355+00:00
-- url     : https://prove2.me/theorems/d2fc01f7-8552-4ed0-b8ca-a27e8f54690c
-- title:
--   Global Theory: injective base Change invariants subtype
-- statement:
--   The Global Theory construction uses the injective base Change invariants subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L210-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L210-L212

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
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Module S M']
  [IsScalarTower R S M']
variable {G : Type*} [Group G]

theorem GlobalTheory.injective_baseChange_invariants_subtype [Module.Flat R S] (ρ : Representation R G M) :
    Function.Injective (ρ.invariants.subtype.baseChange S) := by sorry
