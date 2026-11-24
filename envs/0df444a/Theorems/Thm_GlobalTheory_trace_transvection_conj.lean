-- Prove2me | Theorems.Thm_GlobalTheory_trace_transvection_conj
-- name    : GlobalTheory.trace_transvection_conj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:23:30.264125+00:00
-- url     : https://prove2.me/theorems/25dda007-068b-4883-b8b0-61f39e2c0162
-- title:
--   Global Theory: trace transvection conj
-- statement:
--   The Global Theory construction uses the trace transvection conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsNatMulQuadraticLt.lean#L35-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsNatMulQuadraticLt.lean#L35-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.trace_transvection_conj {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℚ) (x y : n → ℚ) (t : ℚ) :
    ((1 + t • vecMulVec x y)ᵀ * T * (1 + t • vecMulVec x y)).trace =
      T.trace + t * (x ⬝ᵥ T.mulVec y + y ⬝ᵥ T.mulVec x) +
        t ^ 2 * ((y ⬝ᵥ y) * (x ⬝ᵥ T.mulVec x)) := by sorry
