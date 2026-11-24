-- Prove2me | Theorems.Thm_GlobalTheory_sum_Icc_three_quarters_pow_le
-- name    : GlobalTheory.sum_Icc_three_quarters_pow_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:23:00.573881+00:00
-- url     : https://prove2.me/theorems/98aab236-d69f-4b92-b04a-4294353b2315
-- title:
--   Global Theory: sum Icc three quarters pow le
-- statement:
--   The Global Theory construction uses the sum Icc three quarters pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumIccThreeQuartersPowLe.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumIccThreeQuartersPowLe.lean#L7-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeightedFejerPositivityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory

theorem GlobalTheory.sum_Icc_three_quarters_pow_le (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (3 / 4 : ℝ) ^ j ≤ 3 - 3 * (3 / 4 : ℝ) ^ J := by sorry
