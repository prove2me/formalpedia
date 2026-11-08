-- Prove2me | Theorems.Thm_OAI_JointLogSeparation_seven_kernel_twisted_profiles
-- name    : OAI.JointLogSeparation.seven_kernel_twisted_profiles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:20:20.575204+00:00
-- url     : https://prove2.me/theorems/58fb6336-7c7b-46c2-8ae9-df85d7937a0c
-- title:
--   Joint Log Separation: seven kernel twisted profiles
-- statement:
--   The Joint Log Separation construction uses the seven kernel twisted profiles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/ConjugateProfiles.lean#L115-L170
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/ConjugateProfiles.lean#L115-L170

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_UnrestrictedCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ConjugateProfiles
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
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
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
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open OAI.JointLogSeparation
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FourierBridge FirstPassCubeLabels

theorem OAI.JointLogSeparation.seven_kernel_twisted_profiles (g₁ g₂ W : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ), ∀ θ₁ θ₂ : ℝ,
      (∀ z ud ue uv kap x₁ x₂ : ℝ,
        outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂ * (frequencyTwist g₁ θ₁) (z + x₁) * (frequencyTwist g₂ θ₂) (z + x₂) *
          EisensteinSchwartzPoisson.paperRadialFourier W
            (R * Real.exp (kap - ud - 2 * ue - 2 * uv - x₁ - x₂)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          outerWindow V z ud ue uv kap * logPhase (t₁ + t₂) z *
            logPhase t₃ (kap - ud - 2 * ue - 2 * uv) *
            fixedColumnTest (V 5) (t₁ - t₃) x₁ * fixedColumnTest (V 6) (t₂ - t₃) x₂ *
            ((𝓕 (frequencyTwist g₁ θ₁)) t₁ * (𝓕 (frequencyTwist g₂ θ₂)) t₂ * b t₃)) ∧
      (∀ t₁ t₂ t₃ : ℝ, (1 + R) ^ A * ‖(𝓕 (frequencyTwist g₁ θ₁)) t₁ * (𝓕 (frequencyTwist g₂ θ₂)) t₂ * b t₃‖ ≤
        C * (1+‖θ₁‖)^(J+2) * (1+‖θ₂‖)^(J+2) *
          firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by sorry
