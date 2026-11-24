-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_VectorTaylor_step
-- name    : GlobalTheory.CompanionTheory.VectorTaylor.step
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:21:10.006846+00:00
-- url     : https://prove2.me/theorems/8c7ae284-9782-406c-99ac-19641fbe183b
-- title:
--   Vector Taylor: step
-- statement:
--   The Vector Taylor construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnalyticOrthogonalVanishing.lean#L63-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnalyticOrthogonalVanishing.lean#L63-L89

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnalyticOrthogonalVanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VectorTaylor
open Filter Topology

theorem GlobalTheory.CompanionTheory.VectorTaylor.step (f : ℕ → ℝ → ℂ) (B D : ℝ) (hB : 0 ≤ B) (hD : 1 ≤ D)
    (hd : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t)
    (hb : ∀ k t, ‖f k t‖ ≤ B * D ^ k * (k.factorial : ℝ)) (t₀ : ℝ) (h0 : ∀ k, f k t₀ = 0)
    (s : ℝ) (hs : |s| ≤ 1 / (4 * D)) (k : ℕ) : f k (t₀ + s) = 0 := by sorry
