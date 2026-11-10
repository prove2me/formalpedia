-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_canonicalCubeCorrelation_eq_blocks
-- name    : OAI.SecondPassArithmetic.canonicalCubeCorrelation_eq_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:25:39.743208+00:00
-- url     : https://prove2.me/theorems/e14895aa-6abb-408d-9fd0-adb3160954f4
-- title:
--   Second Pass Arithmetic: canonical Cube Correlation eq blocks
-- statement:
--   The Second Pass Arithmetic construction uses the canonical Cube Correlation eq blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/PoissonSource.lean#L667-L712
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/PoissonSource.lean#L667-L712

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_OutsideIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_PoissonSource
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
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
open MixedCrossSeparation (columnCoefficient)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.SecondPassArithmetic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem OAI.SecondPassArithmetic.canonicalCubeCorrelation_eq_blocks
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀i,lambda^2∣p i-1) (pool : Finset ι) (v₁ v₂ : ι→₀ℕ)
    (hB : v₁.support∪v₂.support⊆pool)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂ Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
      ∑A₂∈(v₁.support∪v₂.support).powerset,∑A₁∈(v₁.support∪v₂.support).powerset,
        ∑C∈(pool\(v₁.support∪v₂.support)).powerset,
          canonicalCubeBeforePoisson p hp hcop hg pool ⟨v₁,v₂,A₁,A₂⟩ C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K := by sorry
