-- Prove2me | Theorems.Thm_GlobalTheory_LLeft_summable_nine_pow_mul_inv_sq_succ
-- name    : GlobalTheory.LLeft.summable_nine_pow_mul_inv_sq_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:18.225355+00:00
-- url     : https://prove2.me/theorems/dbf6b1df-9c53-4c89-b703-488acdbdc716
-- title:
--   LLeft: summable nine pow mul inv sq succ
-- statement:
--   The LLeft construction uses the summable nine pow mul inv sq succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L185-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L185-L188

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNinePowMulInvSqSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open GlobalTheory.LLeft

theorem GlobalTheory.LLeft.summable_nine_pow_mul_inv_sq_succ (t : ℝ) (ht : 1 < t) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-t)) := by sorry
