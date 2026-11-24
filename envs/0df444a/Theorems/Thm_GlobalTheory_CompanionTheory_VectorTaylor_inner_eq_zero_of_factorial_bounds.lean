-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_VectorTaylor_inner_eq_zero_of_factorial_bounds
-- name    : GlobalTheory.CompanionTheory.VectorTaylor.inner_eq_zero_of_factorial_bounds
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:53:53.138979+00:00
-- url     : https://prove2.me/theorems/ebbbfb27-e741-4458-9c4c-35f750948200
-- title:
--   Vector Taylor: inner eq zero of factorial bounds
-- statement:
--   The Vector Taylor construction uses the inner eq zero of factorial bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnalyticOrthogonalVanishing.lean#L121-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnalyticOrthogonalVanishing.lean#L121-L154

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

theorem GlobalTheory.CompanionTheory.VectorTaylor.inner_eq_zero_of_factorial_bounds (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (F : ℕ → ℝ → H) (M C : ℝ) (u : H)
    (hd : ∀ k t, HasDerivAt (F k) (F (k + 1) t) t)
    (hb : ∀ k t, ‖F k t‖ ≤ M * C ^ k * (k.factorial : ℝ))
    (h0 : ∀ k, inner ℂ u (F k 0) = 0) : ∀ t, inner ℂ u (F 0 t) = 0 := by sorry
