-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_DilatedGaussian_norm_dilated_le
-- name    : GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.norm_dilated_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:48:12.938797+00:00
-- url     : https://prove2.me/theorems/e745d0af-2530-4e65-8272-0849222fbd3f
-- title:
--   Dilated Gaussian: norm dilated le
-- statement:
--   The Dilated Gaussian construction uses the norm dilated le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedDerivIntegralGaussianExponential.lean#L60-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedDerivIntegralGaussianExponential.lean#L60-L83

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedDerivIntegralGaussianExponential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolMean GlobalTheory.CompanionTheory.HolMean.DilatedGaussian

theorem GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.norm_dilated_le (m n : ℕ) (X : Fin n → ℝ) (z : ℂ)
    (h1 : ∀ j, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re)
    (h2 : ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2) (v : Fin m → Fin n → ℂ) :
    ‖dilated m n X v z‖ ≤ 2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2) := by sorry
