-- Prove2me | Theorems.Thm_OAI_FourierBridge_logProfile_derivative_decay
-- name    : OAI.FourierBridge.logProfile_derivative_decay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:14:42.121661+00:00
-- url     : https://prove2.me/theorems/9d54be3c-318e-4e2a-ab10-b36ee42e90b6
-- title:
--   Fourier Bridge: log Profile derivative decay
-- statement:
--   The Fourier Bridge construction uses the log Profile derivative decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L649-L705
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L649-L705

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

theorem OAI.FourierBridge.logProfile_derivative_decay
    (W F : ℝ → ℂ) (R a m H CW CF : ℝ) (A n : ℕ)
    (hWs : ContDiff ℝ ∞ W) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hWderiv : ∀ i ≤ n, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧ Real.exp (a * y) ≤ H)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF)
    (y : ℝ) :
    m ^ (A + n) * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ n (fun z : ℝ => W z * F (R * Real.exp (a * z))) y‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * CW *
          ((n - i).factorial * CF * (H ^ 2) ^ (n - i)) := by sorry
