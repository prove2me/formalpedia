-- Prove2me | Theorems.Thm_GlobalTheory_kernel_cokernel_length_swap
-- name    : GlobalTheory.kernel_cokernel_length_swap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:02:30.419371+00:00
-- url     : https://prove2.me/theorems/6d1157a5-f75d-4485-b20d-f96feb330234
-- title:
--   Global Theory: kernel cokernel length swap
-- statement:
--   The Global Theory construction uses the kernel cokernel length swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthKerCokerLsmulQuotientSpanSwap.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthKerCokerLsmulQuotientSpanSwap.lean#L85-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem GlobalTheory.kernel_cokernel_length_swap :
    ∀ (A : Type) [CommRing A] [IsDomain A] (a b : A), a ≠ 0 → b ≠ 0 → Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧ Module.length A ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A ((A ⧸ Ideal.span {b}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by sorry
