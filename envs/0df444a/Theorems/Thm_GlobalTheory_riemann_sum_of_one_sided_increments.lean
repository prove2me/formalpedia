-- Prove2me | Theorems.Thm_GlobalTheory_riemann_sum_of_one_sided_increments
-- name    : GlobalTheory.riemann_sum_of_one_sided_increments
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:17:08.773715+00:00
-- url     : https://prove2.me/theorems/e6979d1c-e810-4a08-8662-917cc2f4b5a2
-- title:
--   Global Theory: riemann sum of one sided increments
-- statement:
--   The Global Theory construction uses the riemann sum of one sided increments property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RiemannSumOfOneSidedIncrements.lean#L28-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RiemannSumOfOneSidedIncrements.lean#L28-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RiemannSumOfOneSidedIncrements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory

theorem GlobalTheory.riemann_sum_of_one_sided_increments : ∀ (s : Polynomial ℝ) (ℓ : ℚ → ℕ → ℝ),
    (∀ t t' : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop, ℓ t m - ℓ t' m ≤ ((t' : ℝ) - t) * s.derivative.eval (t : ℝ) + ε) →
    Tendsto (fun m => ℓ 0 m - ℓ 1 m) atTop (𝓝 (s.eval 1 - s.eval 0)) := by sorry
