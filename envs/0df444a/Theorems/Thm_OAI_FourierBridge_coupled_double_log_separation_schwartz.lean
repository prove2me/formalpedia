-- Prove2me | Theorems.Thm_OAI_FourierBridge_coupled_double_log_separation_schwartz
-- name    : OAI.FourierBridge.coupled_double_log_separation_schwartz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T04:57:43.00217+00:00
-- url     : https://prove2.me/theorems/1b99f24e-b8c1-45b4-8b02-b2f52941a014
-- title:
--   Fourier Bridge: coupled double log separation schwartz
-- statement:
--   The Fourier Bridge construction uses the coupled double log separation schwartz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Fourier/PositiveLogProfiles.lean#L124-L241
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Fourier/PositiveLogProfiles.lean#L124-L241

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
open OAI.FourierBridge
open scoped ContDiff FourierTransform SchwartzMap

theorem OAI.FourierBridge.coupled_double_log_separation_schwartz
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F₁ F₂ : 𝓢(ℝ, ℂ))
    (a₁ a₂ M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (A₁ A₂ J₁ J₂ : ℕ) :
    ∃ (b₁ b₂ : ℝ → ℝ → ℂ) (C : ℝ), 0 ≤ C ∧
      ∀ R₁ R₂ : ℝ, 0 ≤ R₁ → 0 ≤ R₂ →
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F₁ (R₁ * Real.exp (∑ j : ι, a₁ j * y j)) *
            F₂ (R₂ * Real.exp (∑ j : ι, a₂ j * y j)) =
          ∫ t₁ : ℝ, (∫ t₂ : ℝ,
            (∏ j : ι, W j (y j)) *
              logPhase t₁ (∑ j : ι, a₁ j * y j) *
              logPhase t₂ (∑ j : ι, a₂ j * y j) *
              b₂ R₂ t₂) * b₁ R₁ t₁) ∧
        ((1 + R₁) ^ A₁ * (1 + R₂) ^ A₂) *
          ((∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ R₁ t₁‖) *
           (∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ R₂ t₂‖)) ≤ C := by sorry
