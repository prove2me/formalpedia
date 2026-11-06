-- Prove2me | Theorems.Thm_OAI_LocalLogFourier_coupled_double_positive_log_separation
-- name    : OAI.LocalLogFourier.coupled_double_positive_log_separation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T04:57:59.108757+00:00
-- url     : https://prove2.me/theorems/7e3f85c7-096d-4127-933c-6f7448de0b85
-- title:
--   Local Log Fourier: coupled double positive log separation
-- statement:
--   The Local Log Fourier construction uses the coupled double positive log separation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Fourier/PositiveLogProfiles.lean#L852-L981
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Fourier/PositiveLogProfiles.lean#L852-L981

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

theorem OAI.LocalLogFourier.coupled_double_positive_log_separation
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F₁ F₂ : ℝ → ℂ)
    (a₁ a₂ M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hFpos₁ : ContDiffOn ℝ ∞ F₁ (Set.Ioi 0))
    (hFpos₂ : ContDiffOn ℝ ∞ F₂ (Set.Ioi 0))
    (A₁ A₂ J₁ J₂ : ℕ) (CF₁ CF₂ : ℝ)
    (hCF₁ : 0 ≤ CF₁) (hCF₂ : 0 ≤ CF₂)
    (hEuler₁ : ∀ i ≤ J₁ + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A₁ * ‖eulerDeriv F₁ i x‖ ≤ CF₁)
    (hEuler₂ : ∀ i ≤ J₂ + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A₂ * ‖eulerDeriv F₂ i x‖ ≤ CF₂) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R₁ R₂ : ℝ, 0 < R₁ → 0 < R₂ →
        ∃ (b₁ b₂ : ℝ → ℂ),
          (∀ y : ι → ℝ,
            (∏ j : ι, W j (y j)) *
              F₁ (R₁ * Real.exp (∑ j : ι, a₁ j * y j)) *
              F₂ (R₂ * Real.exp (∑ j : ι, a₂ j * y j)) =
            ∫ t₁ : ℝ, (∫ t₂ : ℝ,
              (∏ j : ι, W j (y j)) *
                FourierBridge.logPhase t₁ (∑ j : ι, a₁ j * y j) *
                FourierBridge.logPhase t₂ (∑ j : ι, a₂ j * y j) *
                b₂ t₂) * b₁ t₁) ∧
          ((1 + R₁) ^ A₁ * (1 + R₂) ^ A₂) *
            ((∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖) *
             (∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖)) ≤ C := by sorry
