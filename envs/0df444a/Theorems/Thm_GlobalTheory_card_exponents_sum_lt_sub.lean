-- Prove2me | Theorems.Thm_GlobalTheory_card_exponents_sum_lt_sub
-- name    : GlobalTheory.card_exponents_sum_lt_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:52:11.973409+00:00
-- url     : https://prove2.me/theorems/ad4b76e2-1f01-5215-9f21-3aa2a7901d0b
-- title:
--   Global Theory: card exponents sum lt sub
-- statement:
--   The Global Theory construction uses the card exponents sum lt sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardExponentsAndChooseRatioBoundsPair.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardExponentsAndChooseRatioBoundsPair.lean#L7-L14

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

theorem GlobalTheory.card_exponents_sum_lt_sub (D T : ℕ) (hT : D < T) :
    Nat.card {α : Fin D → ℕ // ∑ i, α i < T - D} = (T - 1).choose D := by sorry
