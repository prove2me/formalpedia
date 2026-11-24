-- Prove2me | Theorems.Thm_GlobalTheory_mem_baseChange_invariants_iff
-- name    : GlobalTheory.mem_baseChange_invariants_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:11:40.244183+00:00
-- url     : https://prove2.me/theorems/d0271b8f-cad8-418d-a953-9c8e42a801e6
-- title:
--   Global Theory: mem base Change invariants iff
-- statement:
--   The Global Theory construction uses the mem base Change invariants iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L201-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L201-L208

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

theorem GlobalTheory.mem_baseChange_invariants_iff [Finite G] [Module.Flat R S] (ρ : Representation R G M)
    (x : S ⊗[R] M) :
    x ∈ ρ.invariants.baseChange S ↔ ∀ g, (ρ g).baseChange S x = x := by sorry
