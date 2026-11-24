-- Prove2me | Theorems.Thm_GlobalTheory_tprod_comp_perm
-- name    : GlobalTheory.tprod_comp_perm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:23:48.044983+00:00
-- url     : https://prove2.me/theorems/c09dd8f7-638c-47d8-8664-bd6fefc71abb
-- title:
--   Global Theory: tprod comp perm
-- statement:
--   The Global Theory construction uses the tprod comp perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L540-L564
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L540-L564

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
variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]

theorem GlobalTheory.tprod_comp_perm [Module.Invertible A M] {ι : Type*} [Finite ι] (x : ι → M)
    (σ : Equiv.Perm ι) :
    PiTensorProduct.tprod A (s := fun _ ↦ M) (fun i ↦ x (σ i))
      = PiTensorProduct.tprod A (s := fun _ ↦ M) x := by sorry
