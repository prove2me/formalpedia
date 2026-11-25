-- Prove2me | Theorems.Thm_GlobalTheory_T_card_exponents_and_choose_ratio_bounds_pair
-- name    : GlobalTheory.T.card_exponents_and_choose_ratio_bounds_pair
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:36:59.774855+00:00
-- url     : https://prove2.me/theorems/aba27fc7-c47b-40bd-9e90-99b30b25a780
-- title:
--   T: card exponents and choose ratio bounds pair
-- statement:
--   The T construction uses the card exponents and choose ratio bounds pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardExponentsAndChooseRatioBoundsPairStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardExponentsAndChooseRatioBoundsPairStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardExponentsAndChooseRatioBoundsPair
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BinomRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardExponentsAndChooseRatioBoundsPairStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_exponents_and_choose_ratio_bounds_pair : ∀ (D T : ℕ), (0 < D → D < T → Nat.card {α : Fin D → ℕ // ∑ i, α i < T - D} = (T - 1).choose D) ∧ ∀ (δ d ρ : ℕ), 2 ≤ D → 11 * D ^ 2 ≤ T → d ≤ δ * (T + 2 * D + 6).choose D → (ρ + δ * (T - 1).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) ∧ (ρ + δ * (T + D).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) := by sorry
