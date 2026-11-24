-- Prove2me | Theorems.Thm_GlobalTheory_exists_dual_apply_notMem_of_finite
-- name    : GlobalTheory.exists_dual_apply_notMem_of_finite
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:31:11.220672+00:00
-- url     : https://prove2.me/theorems/fff4b2b4-8c69-4829-959e-b800c46ea948
-- title:
--   Global Theory: exists dual apply not Mem of finite
-- statement:
--   The Global Theory construction uses the exists dual apply not Mem of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L581-L629
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L581-L629

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

theorem GlobalTheory.exists_dual_apply_notMem_of_finite (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Invertible A M] (s : Set (Ideal A)) (hs : s.Finite) (hp : ∀ P ∈ s, P.IsPrime) :
    ∃ (e : M) (f : Module.Dual A M), ∀ P ∈ s, f e ∉ P := by sorry
