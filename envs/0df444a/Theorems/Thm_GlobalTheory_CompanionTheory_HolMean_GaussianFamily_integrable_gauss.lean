-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_GaussianFamily_integrable_gauss
-- name    : GlobalTheory.CompanionTheory.HolMean.GaussianFamily.integrable_gauss
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:46.275688+00:00
-- url     : https://prove2.me/theorems/6cfaf00f-5ac1-4393-87e3-3af35398798b
-- title:
--   Gaussian Family: integrable gauss
-- statement:
--   The Gaussian Family construction uses the integrable gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HolomorphicParameterIntegralGaussianBound.lean#L21-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HolomorphicParameterIntegralGaussianBound.lean#L21-L34

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousOnIteratedDerivFamily
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HolomorphicParameterIntegralGaussianBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolMean GlobalTheory.CompanionTheory.HolMean.GaussianFamily

theorem GlobalTheory.CompanionTheory.HolMean.GaussianFamily.integrable_gauss (m n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun v : Fin m → Fin n → ℂ => Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) := by sorry
