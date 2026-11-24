-- Prove2me | Theorems.Thm_GlobalTheory_T_length_ker_coker_lsmul_quotient_span_swap
-- name    : GlobalTheory.T.length_ker_coker_lsmul_quotient_span_swap
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:51:22.205387+00:00
-- url     : https://prove2.me/theorems/73d5796c-97a3-4ecd-82a0-7734a63880d8
-- title:
--   T: length ker coker lsmul quotient span swap
-- statement:
--   The T construction uses the length ker coker lsmul quotient span swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthKerCokerLsmulQuotientSpanSwapStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthKerCokerLsmulQuotientSpanSwapStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwap
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwapStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.length_ker_coker_lsmul_quotient_span_swap : ∀ (A : Type) [CommRing A] [IsDomain A] (a b : A), a ≠ 0 → b ≠ 0 → Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧ Module.length A ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A ((A ⧸ Ideal.span {b}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by sorry
