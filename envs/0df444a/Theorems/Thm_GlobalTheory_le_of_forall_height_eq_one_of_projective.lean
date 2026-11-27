-- Prove2me | Theorems.Thm_GlobalTheory_le_of_forall_height_eq_one_of_projective
-- name    : GlobalTheory.le_of_forall_height_eq_one_of_projective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:48:25.307842+00:00
-- url     : https://prove2.me/theorems/722cd2a0-87f5-4350-a775-33ebc620de70
-- title:
--   Global Theory: le of forall height eq one of projective
-- statement:
--   The Global Theory construction uses the le of forall height eq one of projective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L235-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L235-L242

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

theorem GlobalTheory.le_of_forall_height_eq_one_of_projective [Module.IsTorsionFree A V]
    {N N' : Submodule A V} [Module.Projective A N']
    (h₀ : ∀ v ∈ N, ∃ a : A, a ≠ 0 ∧ a • v ∈ N')
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → ∀ v ∈ N, ∃ s, s ∉ p ∧ s • v ∈ N') :
    N ≤ N' := by sorry
