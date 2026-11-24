-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_GaussianFamily_integrable_gauss_complex
-- name    : GlobalTheory.CompanionTheory.HolMean.GaussianFamily.integrable_gauss_complex
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:53.291589+00:00
-- url     : https://prove2.me/theorems/74ae043f-f325-40af-b5d6-5343a1f4a3b1
-- title:
--   Gaussian Family: integrable gauss complex
-- statement:
--   The Gaussian Family construction uses the integrable gauss complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HolomorphicParameterIntegralGaussianBound.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HolomorphicParameterIntegralGaussianBound.lean#L10-L19

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

theorem GlobalTheory.CompanionTheory.HolMean.GaussianFamily.integrable_gauss_complex {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun w : ℂ => Real.exp (-δ * ‖w‖ ^ 2)) := by sorry
