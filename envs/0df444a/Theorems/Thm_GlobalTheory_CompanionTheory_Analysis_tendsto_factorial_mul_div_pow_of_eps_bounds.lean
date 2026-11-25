-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Analysis_tendsto_factorial_mul_div_pow_of_eps_bounds
-- name    : GlobalTheory.CompanionTheory.Analysis.tendsto_factorial_mul_div_pow_of_eps_bounds
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:58:39.204632+00:00
-- url     : https://prove2.me/theorems/45d934d4-d553-5b05-bb1e-ca123487f4d7
-- title:
--   Analysis: tendsto factorial mul div pow of eps bounds
-- statement:
--   The Analysis construction uses the tendsto factorial mul div pow of eps bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TendstoOfAsymptoticBounds.lean#L7-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TendstoOfAsymptoticBounds.lean#L7-L29

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TendstoOfAsymptoticBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Analysis

theorem GlobalTheory.CompanionTheory.Analysis.tendsto_factorial_mul_div_pow_of_eps_bounds (f : ℕ → ℝ) (G : ℝ) (D : ℕ)
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (G - ε) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤ f n)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, f n ≤ (G + ε) * (n : ℝ) ^ D / (D.factorial : ℝ)) :
    Tendsto (fun n : ℕ => (D.factorial : ℝ) * f n / (n : ℝ) ^ D) atTop (𝓝 G) := by sorry
