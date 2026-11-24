-- Prove2me | Theorems.Thm_GlobalTheory_mem_range_iff_forall_height_eq_one_of_isReflexive
-- name    : GlobalTheory.mem_range_iff_forall_height_eq_one_of_isReflexive
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:14.088559+00:00
-- url     : https://prove2.me/theorems/a545054b-8f41-4f8c-8c27-53341bd8c227
-- title:
--   Global Theory: mem range iff forall height eq one of is Reflexive
-- statement:
--   The Global Theory construction uses the mem range iff forall height eq one of is Reflexive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L223-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L223-L233

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable {V : Type*} [AddCommGroup V] [Module A V]

theorem GlobalTheory.mem_range_iff_forall_height_eq_one_of_isReflexive [Module.IsReflexive A M]
    (f : M →ₗ[A] V) [IsLocalizedModule A⁰ f] (v : V) :
    v ∈ LinearMap.range f ↔
      ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → ∃ s, s ∉ p ∧ s • v ∈ LinearMap.range f := by sorry
