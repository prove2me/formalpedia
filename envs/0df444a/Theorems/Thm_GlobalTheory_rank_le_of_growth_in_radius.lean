-- Prove2me | Theorems.Thm_GlobalTheory_rank_le_of_growth_in_radius
-- name    : GlobalTheory.rank_le_of_growth_in_radius
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:15:26.816323+00:00
-- url     : https://prove2.me/theorems/d7aceddb-1303-4cd5-a647-4a15c20adcf1
-- title:
--   Global Theory: rank le of growth in radius
-- statement:
--   The Global Theory construction uses the rank le of growth in radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeOfGrowthInRadius.lean#L7-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeOfGrowthInRadius.lean#L7-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeOfGrowthInRadius
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

theorem GlobalTheory.rank_le_of_growth_in_radius : ∀ (D : ℕ) (f : ℝ → ℕ → ℝ) (α γ ρ t₀ t₁ : ℝ), 0 ≤ ρ →
    (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => f t m / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α + γ * t))) →
    (∀ (t : ℝ) (m Q : ℕ), 0 < m → 0 < Q → ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m) ≤ Real.exp (t * m) →
      ρ * (m : ℝ) ^ D * Real.log Q ≤ f t m) → ρ ≤ γ := by sorry
