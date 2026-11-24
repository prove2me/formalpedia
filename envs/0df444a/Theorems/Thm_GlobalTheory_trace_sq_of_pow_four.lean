-- Prove2me | Theorems.Thm_GlobalTheory_trace_sq_of_pow_four
-- name    : GlobalTheory.trace_sq_of_pow_four
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:23:25.930896+00:00
-- url     : https://prove2.me/theorems/fa97be52-f839-437f-b539-c3024984d22f
-- title:
--   Global Theory: trace sq of pow four
-- statement:
--   The Global Theory construction uses the trace sq of pow four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L35-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L35-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {A : Type*} [Fintype A] [DecidableEq A]

theorem GlobalTheory.trace_sq_of_pow_four {U : Matrix A A ℂ} (hU : U ^ 4 = 1) (h2 : (U ^ 2).trace = 1)
    (h13 : U.trace * (U ^ 3).trace = 1) (hodd : Odd (Fintype.card A)) :
    U.trace ^ 2 = (ZMod.χ₄ (Fintype.card A : ZMod 4) : ℤ) := by sorry
