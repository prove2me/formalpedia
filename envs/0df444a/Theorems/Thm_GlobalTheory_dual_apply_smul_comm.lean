-- Prove2me | Theorems.Thm_GlobalTheory_dual_apply_smul_comm
-- name    : GlobalTheory.dual_apply_smul_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:18.426831+00:00
-- url     : https://prove2.me/theorems/94fe17b9-14fa-4360-ab40-d283afb4b4ac
-- title:
--   Global Theory: dual apply smul comm
-- statement:
--   The Global Theory construction uses the dual apply smul comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L528-L532
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L528-L532

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

theorem GlobalTheory.dual_apply_smul_comm [Module.Invertible A M] (f : Module.Dual A M) (x y : M) :
    f x • y = f y • x := by sorry
