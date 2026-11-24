-- Prove2me | Theorems.Thm_GlobalTheory_T_not_mem_Lp_of_growth
-- name    : GlobalTheory.T.not_mem_Lp_of_growth
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:53:47.871397+00:00
-- url     : https://prove2.me/theorems/605ab129-b33a-477c-abc0-f185033d0879
-- title:
--   T: not mem Lp of growth
-- statement:
--   The T construction uses the not mem Lp of growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NotMemLpOfGrowthStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NotMemLpOfGrowthStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NotMemLpOfGrowth
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NotMemLpOfGrowthStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.not_mem_Lp_of_growth : ∀ {X : Type} [MeasurableSpace X] (μ : MeasureTheory.Measure X) (f : X → ℝ) (p : ℝ), 0 < p → MeasureTheory.MemLp f (ENNReal.ofReal p) μ → ∀ (E : ℕ → Set X), (∀ j, MeasurableSet (E j)) → Pairwise (Function.onFun Disjoint E) → ∀ (c D B r : ℝ), 0 < c → 0 < B → 0 ≤ r → (∀ j : ℕ, ENNReal.ofReal (c * D ^ j) ≤ μ (E j)) → (∀ j : ℕ, ∀ x ∈ E j, B * r ^ j ≤ |f x|) → D * r ^ p < 1 := by sorry
