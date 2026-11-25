-- Prove2me | Theorems.Thm_GlobalTheory_T_count_growth_exponential_radii
-- name    : GlobalTheory.T.count_growth_exponential_radii
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:13.437474+00:00
-- url     : https://prove2.me/theorems/445d38d7-ce1f-458b-b6ae-db538d027064
-- title:
--   T: count growth exponential radii
-- statement:
--   The T construction uses the count growth exponential radii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CountGrowthExponentialRadiiStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CountGrowthExponentialRadiiStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CountGrowthExponentialRadii
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CountGrowthExponentialRadiiStatement
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

theorem GlobalTheory.T.count_growth_exponential_radii : ∀ (D e δ : ℕ) (N : ℕ → ℝ → ℕ) (κ t : ℝ), 0 < e → 0 < κ → κ ≤ 1 → 0 < t → (∀ m, ∀ R R' : ℝ, 0 ≤ R → R ≤ R' → N m R ≤ N m R') → (∀ s : ℕ, s < e → ∃ (c c' : ℕ) (C C' : ℝ), 0 < C ∧ 0 < C' ∧ ∀ (q : ℕ) (R : ℝ), 0 ≤ R → (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ≤ N (e * (q + c) + s) (C * (q + D).choose D * R) ∧ N (e * q + s) R ≤ (2 * ⌊C' * R / κ ^ (q + c')⌋₊ + 1) ^ (δ * (q + c' + D).choose D)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, δ / ((e : ℝ) ^ D * D.factorial) * t - ε ≤ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ∧ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ≤ δ / ((e : ℝ) ^ D * D.factorial) * (t - Real.log κ / e) + ε := by sorry
