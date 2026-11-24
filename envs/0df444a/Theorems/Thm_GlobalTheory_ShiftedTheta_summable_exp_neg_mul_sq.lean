-- Prove2me | Theorems.Thm_GlobalTheory_ShiftedTheta_summable_exp_neg_mul_sq
-- name    : GlobalTheory.ShiftedTheta.summable_exp_neg_mul_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:45:54.642289+00:00
-- url     : https://prove2.me/theorems/56910628-f531-4dfe-bfa1-b5d6a632cd1d
-- title:
--   Shifted Theta: summable exp neg mul sq
-- statement:
--   The Shifted Theta construction uses the summable exp neg mul sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableExpNegMulSq.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableExpNegMulSq.lean#L37-L42

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

theorem GlobalTheory.ShiftedTheta.summable_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-(c * (n : ℝ) ^ 2)) := by sorry
