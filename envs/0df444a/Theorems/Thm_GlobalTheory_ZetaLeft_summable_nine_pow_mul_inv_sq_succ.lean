-- Prove2me | Theorems.Thm_GlobalTheory_ZetaLeft_summable_nine_pow_mul_inv_sq_succ
-- name    : GlobalTheory.ZetaLeft.summable_nine_pow_mul_inv_sq_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:00:11.619791+00:00
-- url     : https://prove2.me/theorems/ae8a6562-4c37-4acb-acfe-f53a0eb4f349
-- title:
--   Zeta Left: summable nine pow mul inv sq succ
-- statement:
--   The Zeta Left construction uses the summable nine pow mul inv sq succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean#L92-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open GlobalTheory GlobalTheory.ZetaLeft

theorem GlobalTheory.ZetaLeft.summable_nine_pow_mul_inv_sq_succ : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(9/8 : ℝ))) := by sorry
