-- Prove2me | Theorems.Thm_GlobalTheory_IntegrableExpNegAbs_integrable_exp_neg_mul_abs
-- name    : GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:19:20.245378+00:00
-- url     : https://prove2.me/theorems/afb01525-1bad-4b87-9eee-46e2c34bbb1f
-- title:
--   Integrable Exp Neg Abs: integrable exp neg mul abs
-- statement:
--   The Integrable Exp Neg Abs construction uses the integrable exp neg mul abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegrableExpNegMulAbs.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegrableExpNegMulAbs.lean#L7-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegrableExpNegMulAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegrableExpNegAbs
open MeasureTheory Set

theorem GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs {c : ℝ} (hc : (0 : ℝ) < c) :
    MeasureTheory.Integrable (fun (s : ℝ) ↦ Real.exp (-(c * |s|))) MeasureTheory.MeasureSpace.volume := by sorry
