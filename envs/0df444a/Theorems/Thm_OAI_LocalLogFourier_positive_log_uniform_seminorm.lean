-- Prove2me | Theorems.Thm_OAI_LocalLogFourier_positive_log_uniform_seminorm
-- name    : OAI.LocalLogFourier.positive_log_uniform_seminorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T04:57:41.679806+00:00
-- url     : https://prove2.me/theorems/15bf4ef8-4968-4dce-8d28-64dd42869743
-- title:
--   Local Log Fourier: positive log uniform seminorm
-- statement:
--   The Local Log Fourier construction uses the positive log uniform seminorm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Fourier/PositiveLogProfiles.lean#L429-L511
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Fourier/PositiveLogProfiles.lean#L429-L511

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic
open ActualEisensteinCubic
open Filter
open scoped Topology
open ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open OAI.LocalLogFourier

theorem OAI.LocalLogFourier.positive_log_uniform_seminorm
    (V F : ℝ → ℂ) (R m Lwin CW CF : ℝ) (A n k : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ n, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin)
    (hEuler : ∀ i ≤ n, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    m ^ A * (1 + R) ^ A *
      (SchwartzMap.seminorm ℝ k n)
        (positiveLogProfile V F R hVc hVs hFpos hR) ≤
      Lwin ^ k *
        (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF) := by sorry
