-- Prove2me | Theorems.Thm_GlobalTheory_isBaseChange_invariants_subtype
-- name    : GlobalTheory.isBaseChange_invariants_subtype
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:47:05.854392+00:00
-- url     : https://prove2.me/theorems/020d1703-2a02-469a-8d02-b4e6fd4b323d
-- title:
--   Global Theory: is Base Change invariants subtype
-- statement:
--   The Global Theory construction uses the is Base Change invariants subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L772-L779
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L772-L779

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
variable {G : Type*} [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
variable (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
variable {A M}
variable (B : Type*) [CommRing B] [Algebra B A] [FaithfulSMul B A] [SMulCommClass G B A]
  [Algebra.IsInvariant B A G] [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]

theorem GlobalTheory.isBaseChange_invariants_subtype {n : M}
    (hn : Function.Bijective (LinearMap.toSpanSingleton A M n)) (hn' : ∀ g : G, g • n = n) :
    IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype := by sorry
