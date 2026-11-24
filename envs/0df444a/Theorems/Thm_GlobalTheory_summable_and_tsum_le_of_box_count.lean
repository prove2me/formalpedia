-- Prove2me | Theorems.Thm_GlobalTheory_summable_and_tsum_le_of_box_count
-- name    : GlobalTheory.summable_and_tsum_le_of_box_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:57.6288+00:00
-- url     : https://prove2.me/theorems/09443aae-ad18-49ab-8c4c-8996ae53ba07
-- title:
--   Global Theory: summable and tsum le of box count
-- statement:
--   The Global Theory construction uses the summable and tsum le of box count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SummableAndTsumLeOfBoxCount.lean#L7-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SummableAndTsumLeOfBoxCount.lean#L7-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SummableAndTsumLeOfBoxCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory

theorem GlobalTheory.summable_and_tsum_le_of_box_count (ι Γ : Type) [Fintype ι] (D : Γ → ι → ℝ) (t : Γ → ℝ)
    (a A c : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (ha : Real.exp (-a) ≤ 1 / 2) (_hD : ∀ γ v, 0 ≤ D γ v)
    (ht : ∀ γ, 0 ≤ t γ ∧ t γ ≤ c * ∏ v, Real.exp (-(2 * a * (⌊D γ v⌋₊ : ℝ))))
    (hN : ∀ r : ι → ℝ, (∀ v, 0 ≤ r v) → {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.Finite ∧
      (({γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.ncard : ℕ) : ℝ) ≤ A * Real.exp (a * ∑ v, r v)) :
    Summable t ∧ ∑' γ, t γ ≤ c * A * (2 * Real.exp a) ^ Fintype.card ι := by sorry
