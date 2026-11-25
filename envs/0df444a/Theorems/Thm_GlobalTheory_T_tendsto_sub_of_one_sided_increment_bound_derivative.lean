-- Prove2me | Theorems.Thm_GlobalTheory_T_tendsto_sub_of_one_sided_increment_bound_derivative
-- name    : GlobalTheory.T.tendsto_sub_of_one_sided_increment_bound_derivative
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:39:39.086803+00:00
-- url     : https://prove2.me/theorems/6c5ae76a-7847-56e2-9e6b-a4387f0205d0
-- title:
--   T: tendsto sub of one sided increment bound derivative
-- statement:
--   The T construction uses the tendsto sub of one sided increment bound derivative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RiemannSumOfOneSidedIncrementsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RiemannSumOfOneSidedIncrementsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RiemannSumOfOneSidedIncrements
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RiemannSumOfOneSidedIncrementsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.tendsto_sub_of_one_sided_increment_bound_derivative : ∀ (s : Polynomial ℝ) (ℓ : ℚ → ℕ → ℝ), (∀ t t' : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ℓ t m - ℓ t' m ≤ ((t' : ℝ) - t) * s.derivative.eval (t : ℝ) + ε) → Tendsto (fun m => ℓ 0 m - ℓ 1 m) atTop (𝓝 (s.eval 1 - s.eval 0)) := by sorry
