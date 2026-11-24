-- Prove2me | Theorems.Thm_GlobalTheory_bddAbove_of_spanning_periods
-- name    : GlobalTheory.bddAbove_of_spanning_periods
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:06:33.334731+00:00
-- url     : https://prove2.me/theorems/03062f38-24cc-4fb4-a416-241e6ec77e5c
-- title:
--   Global Theory: bdd Above of spanning periods
-- statement:
--   The Global Theory construction uses the bdd Above of spanning periods property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BddAboveOfSpanningPeriods.lean#L5-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BddAboveOfSpanningPeriods.lean#L5-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BddAboveOfSpanningPeriods
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.bddAbove_of_spanning_periods (R : Type) [NormedAddCommGroup R] [NormedSpace ℝ R]
    [FiniteDimensional ℝ R] (g : R → ℝ) (hg : Continuous g) (S : Set R)
    (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ s ∈ S, ∃ N : ℕ, 0 < N ∧ ∀ x, g (x + (N : ℝ) • s) = g x) :
    ∃ C : ℝ, ∀ x, g x ≤ C := by sorry
