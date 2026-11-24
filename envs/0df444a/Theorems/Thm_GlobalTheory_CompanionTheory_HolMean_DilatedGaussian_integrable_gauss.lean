-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_DilatedGaussian_integrable_gauss
-- name    : GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.integrable_gauss
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:48:15.404805+00:00
-- url     : https://prove2.me/theorems/768c64ef-0065-43bf-82ab-8a9ae5757829
-- title:
--   Dilated Gaussian: integrable gauss
-- statement:
--   The Dilated Gaussian construction uses the integrable gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedDerivIntegralGaussianExponential.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedDerivIntegralGaussianExponential.lean#L16-L26

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

theorem GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.integrable_gauss (m n : ℕ) :
    Integrable (fun v : Fin m → Fin n → ℂ =>
      Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2)) := by sorry
