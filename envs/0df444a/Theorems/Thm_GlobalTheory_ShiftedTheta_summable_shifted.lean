-- Prove2me | Theorems.Thm_GlobalTheory_ShiftedTheta_summable_shifted
-- name    : GlobalTheory.ShiftedTheta.summable_shifted
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:11:38.060331+00:00
-- url     : https://prove2.me/theorems/7165e0a7-0d76-4534-a9bc-e4cbc6ffe074
-- title:
--   Shifted Theta: summable shifted
-- statement:
--   The Shifted Theta construction uses the summable shifted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableExpNegMulSq.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableExpNegMulSq.lean#L44-L49

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

theorem GlobalTheory.ShiftedTheta.summable_shifted {s : ℝ} (θ : ℝ) (hs : 0 < s) :
    Summable fun m : ℤ => Real.exp (-(s * (m + θ) ^ 2)) := by sorry
