-- Prove2me | Theorems.Thm_GlobalTheory_smul_tensorNorm
-- name    : GlobalTheory.smul_tensorNorm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:40.531938+00:00
-- url     : https://prove2.me/theorems/b544698d-f93f-4c3b-a676-6e5b8dc90572
-- title:
--   Global Theory: smul tensor Norm
-- statement:
--   The Global Theory construction uses the smul tensor Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L847-L852
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L847-L852

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

theorem GlobalTheory.smul_tensorNorm [Finite G] [Module.Invertible A M] (κ : ι ≃ G) (x : M) (g : G) :
    letI := piTensorDistribMulAction G A (fun _ : ι ↦ M)
    g • tensorNorm A κ x = tensorNorm A κ x := by sorry
