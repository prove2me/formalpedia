-- Prove2me | Theorems.Thm_GlobalTheory_height_eq_one_of_mem_associatedPrimes_coker_of_dual
-- name    : GlobalTheory.height_eq_one_of_mem_associatedPrimes_coker_of_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:38.982869+00:00
-- url     : https://prove2.me/theorems/dacf9e3c-eedd-4c09-9472-3e0b50baac32
-- title:
--   Global Theory: height eq one of mem associated Primes coker of dual
-- statement:
--   The Global Theory construction uses the height eq one of mem associated Primes coker of dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L253-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L253-L272

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

theorem GlobalTheory.height_eq_one_of_mem_associatedPrimes_coker_of_dual
    (hM : ∀ {a : A}, a ≠ 0 → ∀ {m : M}, (∀ φ : Module.Dual A M, a ∣ φ m) → ∃ m', a • m' = m)
    (f : M →ₗ[A] V) (hf : Function.Injective f) [Module.IsTorsionFree A V]
    (ht : ∀ v : V, ∃ a : A, a ≠ 0 ∧ a • v ∈ LinearMap.range f) {p : Ideal A}
    (hp : p ∈ associatedPrimes A (V ⧸ LinearMap.range f)) : p.height = 1 := by sorry
