-- Prove2me | Theorems.Thm_GlobalTheory_FlowProgramme_optimum
-- name    : GlobalTheory.FlowProgramme.optimum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:15:41.718666+00:00
-- url     : https://prove2.me/theorems/8fd3c1ea-e701-41b1-b83e-b2d3e5edc4a7
-- title:
--   Flow Programme: optimum
-- statement:
--   The Flow Programme construction uses the optimum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CyclicSolvable.lean#L120-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CyclicSolvable.lean#L120-L162

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_WtSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CyclicSolvable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory GlobalTheory.FlowProgramme

theorem GlobalTheory.FlowProgramme.optimum (l d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) (hX : ∀ a, 0 ≤ X a) :
    ∃ x : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a) ∧ ∀ x' : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x' a i) ∧ (∀ a i, x' a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x' a i + ∑ i ∈ Finset.range d, x' (a - i) i ≤ X a) →
      ∑ a, ∑ i ∈ Finset.range d, x' a i ≤ ∑ a, ∑ i ∈ Finset.range d, x a i := by sorry
