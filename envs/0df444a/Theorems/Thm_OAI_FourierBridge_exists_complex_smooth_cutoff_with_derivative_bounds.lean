-- Prove2me | Theorems.Thm_OAI_FourierBridge_exists_complex_smooth_cutoff_with_derivative_bounds
-- name    : OAI.FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:15:08.127115+00:00
-- url     : https://prove2.me/theorems/c24f0d8a-8e4a-4a39-9b15-98ce51572df8
-- title:
--   Fourier Bridge: exists complex smooth cutoff with derivative bounds
-- statement:
--   The Fourier Bridge construction uses the exists complex smooth cutoff with derivative bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L1270-L1306
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L1270-L1306

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

theorem OAI.FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds
    (T : ℝ) (K : ℕ) (hT : 0 ≤ T) :
    ∃ (V : ℝ → ℂ) (CW : ℝ),
      HasCompactSupport V ∧ ContDiff ℝ ∞ V ∧
      (∀ s, |s| ≤ T → V s = 1) ∧
      0 ≤ CW ∧
      (∀ i ≤ K, ∀ y, ‖iteratedFDeriv ℝ i V y‖ ≤ CW) ∧
      (∀ y,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V y‖ ≠ 0) →
          Real.exp (-(T + 1)) ≤ Real.exp y ∧
          Real.exp y ≤ Real.exp (T + 1) ∧ |y| ≤ T + 1) := by sorry
