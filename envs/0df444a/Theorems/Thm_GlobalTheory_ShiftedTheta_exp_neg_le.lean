-- Prove2me | Theorems.Thm_GlobalTheory_ShiftedTheta_exp_neg_le
-- name    : GlobalTheory.ShiftedTheta.exp_neg_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:11:40.107628+00:00
-- url     : https://prove2.me/theorems/f76677ab-59a1-4f06-98b6-78f4a76d9d53
-- title:
--   Shifted Theta: exp neg le
-- statement:
--   The Shifted Theta construction uses the exp neg le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableExpNegMulSq.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableExpNegMulSq.lean#L17-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableExpNegMulSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ShiftedTheta

theorem GlobalTheory.ShiftedTheta.exp_neg_le {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 2 / y ^ 2 := by sorry
