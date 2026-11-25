-- Prove2me | Theorems.Thm_GlobalTheory_FlowProgramme_duality
-- name    : GlobalTheory.FlowProgramme.duality
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:01.530789+00:00
-- url     : https://prove2.me/theorems/3ce04fa1-8a28-4a1e-aa30-97c75ee632e5
-- title:
--   Flow Programme: duality
-- statement:
--   The Flow Programme construction uses the duality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CyclicSolvable.lean#L13-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CyclicSolvable.lean#L13-L55

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

theorem GlobalTheory.FlowProgramme.duality (l d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) (x : ZMod d → ℕ → ℝ)
    (hx : ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a)) :
    ((l : ℝ) + 1) * ∑ a, ∑ i ∈ Finset.range d, x a i ≤ ∑ a, X a ∧
      ∀ i₀ : ℕ, ∑ a, ∑ i ∈ Finset.Ico i₀ d, x a i ≤ ((l : ℝ) ^ i₀)⁻¹ * ∑ a, X a := by sorry
