-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_DilatedGaussian_eventually_small
-- name    : GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.eventually_small
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:48:09.571545+00:00
-- url     : https://prove2.me/theorems/729954a2-c689-4a7e-930d-abfbeeb37c62
-- title:
--   Dilated Gaussian: eventually small
-- statement:
--   The Dilated Gaussian construction uses the eventually small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedDerivIntegralGaussianExponential.lean#L46-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedDerivIntegralGaussianExponential.lean#L46-L58

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

theorem GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.eventually_small (m n : ℕ) (X : Fin n → ℝ) :
    ∀ᶠ z : ℂ in 𝓝 0, (∀ j, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re) ∧
      ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2 := by sorry
