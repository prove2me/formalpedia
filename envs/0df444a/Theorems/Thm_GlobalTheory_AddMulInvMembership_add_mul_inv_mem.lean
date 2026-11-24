-- Prove2me | Theorems.Thm_GlobalTheory_AddMulInvMembership_add_mul_inv_mem
-- name    : GlobalTheory.AddMulInvMembership.add_mul_inv_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:53:09.006657+00:00
-- url     : https://prove2.me/theorems/93b8fc99-e538-461c-8c2a-a09c24b9da21
-- title:
--   Add Mul Inv Membership: add mul inv mem
-- statement:
--   The Add Mul Inv Membership construction uses the add mul inv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddMulInvMem.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddMulInvMem.lean#L7-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.AddMulInvMembership

theorem GlobalTheory.AddMulInvMembership.add_mul_inv_mem :
    (let d1 : {K : Type u_1} → [inst : Field K] → Subring K → K → K → Prop :=
      @(fun {K : Type u_1} [Field K] (S : Subring K) (π a : K) ↦ a * π⁻¹ ∈ S);
    ∀ {K : Type u_1} [inst : Field K] [StarRing K] {S : Subring K} {π a b : K},
      d1 S π a → d1 S π b → d1 S π (a + b)) := by sorry
