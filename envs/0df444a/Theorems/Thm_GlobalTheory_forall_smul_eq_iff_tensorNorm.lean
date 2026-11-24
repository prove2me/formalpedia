-- Prove2me | Theorems.Thm_GlobalTheory_forall_smul_eq_iff_tensorNorm
-- name    : GlobalTheory.forall_smul_eq_iff_tensorNorm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:51:40.202358+00:00
-- url     : https://prove2.me/theorems/bbead419-03bd-4dcf-94ed-e81ea3b5bd51
-- title:
--   Global Theory: forall smul eq iff tensor Norm
-- statement:
--   The Global Theory construction uses the forall smul eq iff tensor Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L874-L882
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L874-L882

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
variable {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] {ι : Type*}
variable [SMulDistribClass G A M]
variable {A}

theorem GlobalTheory.forall_smul_eq_iff_tensorNorm [Finite G] (κ : ι ≃ G) {e : M}
    (he : Function.Bijective (LinearMap.toSpanSingleton A M e)) (y : ⨂[A] _ : ι, M) :
    letI := piTensorDistribMulAction G A (fun _ : ι ↦ M)
    (∀ g : G, g • y = y) ↔ ∃ a ∈ FixedPoints.subring A G, y = a • tensorNorm A κ e := by sorry
