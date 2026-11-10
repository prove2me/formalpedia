-- Prove2me | Theorems.Thm_OAI_SecondPassIntegration_full_uniform_normalized_child_tests
-- name    : OAI.SecondPassIntegration.full_uniform_normalized_child_tests
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T06:25:15.479947+00:00
-- url     : https://prove2.me/theorems/ba66c7ab-e704-4f3a-8ba7-3dd7c5996215
-- title:
--   Second Pass Integration: full uniform normalized child tests
-- statement:
--   The Second Pass Integration construction uses the full uniform normalized child tests property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CompactProfiles.lean#L352-L398
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CompactProfiles.lean#L352-L398

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactProfiles
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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.SecondPassIntegration
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels SecondPassArithmetic

theorem OAI.SecondPassIntegration.full_uniform_normalized_child_tests
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg₁ : ∀ s, g₁ s ≠ 0 → |s| ≤ A) (hg₂ : ∀ s, g₂ s ≠ 0 → |s| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
      ∀ (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O),
        d ≠ 0 → e ≠ 0 → k ≠ 0 →
        |Real.log (primeProductNorm p V * X₀ / X)| ≤ B →
        |Real.log (elementNorm d / D)| ≤ B →
        |Real.log (elementNorm e / E)| ≤ B →
        |Real.log (primeProductNorm p V / V₀)| ≤ B →
        |Real.log (elementNorm (d*e*k) / K)| ≤ B →
        secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k (-k)
          (radialPairKernel p e k W g₁ g₂ X X Y) =
        (X : ℂ)⁻¹ * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*r)
          (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) A₁ A₂ W windows
          (Real.log (primeProductNorm p V * X₀ / X)) (Real.log (elementNorm d / D))
          (Real.log (elementNorm e / E)) (Real.log (primeProductNorm p V / V₀))
          (Real.log (elementNorm (d*e*k) / K)) X₀ X₀ (Y*K/(D*E^2*V₀^2*X₀^2)) := by sorry
