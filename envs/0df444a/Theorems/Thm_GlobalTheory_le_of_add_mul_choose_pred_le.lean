-- Prove2me | Theorems.Thm_GlobalTheory_le_of_add_mul_choose_pred_le
-- name    : GlobalTheory.le_of_add_mul_choose_pred_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:56:14.921106+00:00
-- url     : https://prove2.me/theorems/f4d08dc2-6892-508e-bdbd-3db7cd7ba9a0
-- title:
--   Global Theory: le of add mul choose pred le
-- statement:
--   The Global Theory construction uses the le of add mul choose pred le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardExponentsAndChooseRatioBoundsPair.lean#L16-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardExponentsAndChooseRatioBoundsPair.lean#L16-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BinomRatio
import Definitions.Def_ReciprocityTheory_SemistableReduction_FinrankRestrictTotalDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardExponentsAndChooseRatioBoundsPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.le_of_add_mul_choose_pred_le (D T δ d ρ : ℕ) (hD : 2 ≤ D) (hT : 11 * D ^ 2 ≤ T)
    (hd : d ≤ δ * (T + 2 * D + 6).choose D) (hρ : ρ + δ * (T - 1).choose D ≤ d) :
    (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T := by sorry
