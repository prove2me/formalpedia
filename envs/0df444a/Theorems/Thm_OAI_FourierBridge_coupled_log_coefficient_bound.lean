-- Prove2me | Theorems.Thm_OAI_FourierBridge_coupled_log_coefficient_bound
-- name    : OAI.FourierBridge.coupled_log_coefficient_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:15:08.349813+00:00
-- url     : https://prove2.me/theorems/1a911eb7-86d5-44a0-bec1-fc290ae0d18b
-- title:
--   Fourier Bridge: coupled log coefficient bound
-- statement:
--   The Fourier Bridge construction uses the coupled log coefficient bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L1433-L1473
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L1433-L1473

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff Manifold
open OAI.FourierBridge

theorem OAI.FourierBridge.coupled_log_coefficient_bound
    (V F : ℝ → ℂ) (R m H L CW CF : ℝ) (A J : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (hL : 0 ≤ L)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ y,
      ‖iteratedFDeriv ℝ i V y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i V y‖ ≠ 0) →
        m ≤ Real.exp y ∧ Real.exp y ≤ H ∧ |y| ≤ L)
    (hFdecay : ∀ j ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ i ≤ j, ∀ u, 0 ≤ u →
        (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    (m ^ (A + (J + (volume : Measure ℝ).integrablePower)) *
      (1 + R) ^ A) *
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (logProfile V F R 1 hVc hVs hFs)) t‖) ≤
      (2 : ℝ) ^ J *
        (coefficientMomentBound 0
          (profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
            L H CW CF) +
        coefficientMomentBound J
          (profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
            L H CW CF)) := by sorry
