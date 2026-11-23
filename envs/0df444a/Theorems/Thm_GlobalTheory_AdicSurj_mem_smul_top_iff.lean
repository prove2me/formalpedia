-- Prove2me | Theorems.Thm_GlobalTheory_AdicSurj_mem_smul_top_iff
-- name    : GlobalTheory.AdicSurj.mem_smul_top_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:49.91626+00:00
-- url     : https://prove2.me/theorems/e10510a0-4358-4095-a6ce-df554e26a407
-- title:
--   Adic Surj: mem smul top iff
-- statement:
--   The Adic Surj construction uses the mem smul top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionTensorQuotientRingEquiv.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionTensorQuotientRingEquiv.lean#L11-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionTensorQuotientRingEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.AdicSurj
open AdicCompletion
variable (B : Type) {A : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)

theorem GlobalTheory.AdicSurj.mem_smul_top_iff (n : ℕ) (b : B) :
    b ∈ (J ^ n • ⊤ : Submodule A B) ↔ b ∈ (J.map (algebraMap A B)) ^ n := by sorry
