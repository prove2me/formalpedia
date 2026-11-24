-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_VectorTaylor_iter_bound
-- name    : GlobalTheory.CompanionTheory.VectorTaylor.iter_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:21:35.596894+00:00
-- url     : https://prove2.me/theorems/e0769a35-c1bf-4526-bbe8-b0faa0184a54
-- title:
--   Vector Taylor: iter bound
-- statement:
--   The Vector Taylor construction uses the iter bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnalyticOrthogonalVanishing.lean#L36-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnalyticOrthogonalVanishing.lean#L36-L61

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

theorem GlobalTheory.CompanionTheory.VectorTaylor.iter_bound (f : ℕ → ℝ → ℂ) (A : ℕ → ℝ)
    (hd : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t)
    (hb : ∀ k t, ‖f k t‖ ≤ A k) (t₀ : ℝ) (h0 : ∀ k, f k t₀ = 0) (n : ℕ) :
    ∀ k s, ‖f k (t₀ + s)‖ ≤ A (k + n) * |s| ^ n / n.factorial := by sorry
