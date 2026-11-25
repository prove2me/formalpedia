-- Prove2me | Theorems.Thm_GlobalTheory_T_sum_fibre_two_index_encard_bound
-- name    : GlobalTheory.T.sum_fibre_two_index_encard_bound
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:47:24.919103+00:00
-- url     : https://prove2.me/theorems/f08b7ec5-93d7-4205-a6cb-ff95fd93c92e
-- title:
--   T: sum fibre two index encard bound
-- statement:
--   The T construction uses the sum fibre two index encard bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SumFibreTwoIndexEncardBoundStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SumFibreTwoIndexEncardBoundStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumFibreTwoIndexEncardBound
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumFibreTwoIndexEncardBoundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.sum_fibre_two_index_encard_bound : ∀ (α Θ : Type) (S : Finset α) (xf yf : α → ℕ) (Φ : α → Θ) (Tr : ℕ → ℕ → Set Θ) (f : α → ℝ) (B₁ B₂ : ℕ → ℝ) (R₁ R₂ : Finset ℕ), (∀ a ∈ S, 0 ≤ f a) → (∀ a ∈ S, xf a ∈ R₁ ∧ yf a ∈ R₂ ∧ Φ a ∈ Tr (xf a) (yf a)) → (∀ a ∈ S, ∑ b ∈ S.filter (fun b => Φ b = Φ a ∧ xf b = xf a ∧ yf b = yf a), f b ≤ B₁ (xf a) * B₂ (yf a)) → ENNReal.ofReal (∑ a ∈ S, f a) ≤ ∑ x ∈ R₁, ∑ y ∈ R₂, (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by sorry
