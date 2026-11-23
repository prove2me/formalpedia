-- Prove2me | Theorems.Thm_GlobalTheory_forall_smul_eq_iff_of_invariant_generator
-- name    : GlobalTheory.forall_smul_eq_iff_of_invariant_generator
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:13.177546+00:00
-- url     : https://prove2.me/theorems/b64ed788-7a4d-4b3b-ba36-673a38c8170e
-- title:
--   Global Theory: forall smul eq iff of invariant generator
-- statement:
--   The Global Theory construction uses the forall smul eq iff of invariant generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L744-L753
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L744-L753

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

theorem GlobalTheory.forall_smul_eq_iff_of_invariant_generator {n : M}
    (hn : Function.Bijective (LinearMap.toSpanSingleton A M n)) (hn' : ∀ g : G, g • n = n)
    (y : M) : (∀ g : G, g • y = y) ↔ ∃ a ∈ FixedPoints.subring A G, y = a • n := by sorry
