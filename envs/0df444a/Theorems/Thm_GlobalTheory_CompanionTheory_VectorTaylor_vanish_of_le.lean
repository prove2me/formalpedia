-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_VectorTaylor_vanish_of_le
-- name    : GlobalTheory.CompanionTheory.VectorTaylor.vanish_of_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:21:13.109408+00:00
-- url     : https://prove2.me/theorems/acdc37e1-c3ba-4ee6-a8c4-778798764f1c
-- title:
--   Vector Taylor: vanish of le
-- statement:
--   The Vector Taylor construction uses the vanish of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnalyticOrthogonalVanishing.lean#L91-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnalyticOrthogonalVanishing.lean#L91-L119

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

theorem GlobalTheory.CompanionTheory.VectorTaylor.vanish_of_le (f : ℕ → ℝ → ℂ) (B D : ℝ) (hB : 0 ≤ B) (hD : 1 ≤ D)
    (hd : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t)
    (hb : ∀ k t, ‖f k t‖ ≤ B * D ^ k * (k.factorial : ℝ)) (h0 : ∀ k, f k 0 = 0) (m : ℕ) :
    ∀ t : ℝ, |t| ≤ m * (1 / (4 * D)) → ∀ k, f k t = 0 := by sorry
