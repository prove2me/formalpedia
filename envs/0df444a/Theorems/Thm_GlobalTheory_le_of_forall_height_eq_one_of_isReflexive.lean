-- Prove2me | Theorems.Thm_GlobalTheory_le_of_forall_height_eq_one_of_isReflexive
-- name    : GlobalTheory.le_of_forall_height_eq_one_of_isReflexive
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:48:25.391523+00:00
-- url     : https://prove2.me/theorems/58b328b4-a65c-43b1-bd74-2723e4a5ac0d
-- title:
--   Global Theory: le of forall height eq one of is Reflexive
-- statement:
--   The Global Theory construction uses the le of forall height eq one of is Reflexive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L244-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L244-L251

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

theorem GlobalTheory.le_of_forall_height_eq_one_of_isReflexive [Module.IsTorsionFree A V]
    {N N' : Submodule A V} [Module.IsReflexive A N']
    (h₀ : ∀ v ∈ N, ∃ a : A, a ≠ 0 ∧ a • v ∈ N')
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → ∀ v ∈ N, ∃ s, s ∉ p ∧ s • v ∈ N') :
    N ≤ N' := by sorry
