-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_iteratedDeriv_series
-- name    : GlobalTheory.CompanionTheory.HolMean.iteratedDeriv_series
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:47.624797+00:00
-- url     : https://prove2.me/theorems/39f4c9cf-776c-4b1b-af07-52aff1971c12
-- title:
--   Hol Mean: iterated Deriv series
-- statement:
--   The Hol Mean construction uses the iterated Deriv series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AesmIteratedDerivReal.lean#L61-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AesmIteratedDerivReal.lean#L61-L88

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolMean
variable {κ : Type} {U : Set ℂ}

theorem GlobalTheory.CompanionTheory.HolMean.iteratedDeriv_series (hU : IsOpen U) (r : ℕ) : ∀ (F : κ → ℂ → ℂ),
    (∀ k, DifferentiableOn ℂ (F k) U) →
    (∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ u : κ → ℝ, Summable u ∧ ∀ z ∈ V ∩ U, ∀ k, ‖F k z‖ ≤ u k) →
    ∀ z ∈ U, iteratedDeriv r (fun w => ∑' k, F k w) z = ∑' k, iteratedDeriv r (F k) z := by sorry
