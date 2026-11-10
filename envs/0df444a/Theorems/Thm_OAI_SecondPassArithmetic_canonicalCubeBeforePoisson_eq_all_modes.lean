-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_canonicalCubeBeforePoisson_eq_all_modes
-- name    : OAI.SecondPassArithmetic.canonicalCubeBeforePoisson_eq_all_modes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:25:38.247562+00:00
-- url     : https://prove2.me/theorems/3d67a450-ca49-48f6-9b45-1e85203b7e6e
-- title:
--   Second Pass Arithmetic: canonical Cube Before Poisson eq all modes
-- statement:
--   The Second Pass Arithmetic construction uses the canonical Cube Before Poisson eq all modes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/PoissonSource.lean#L714-L731
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/PoissonSource.lean#L714-L731

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

theorem OAI.SecondPassArithmetic.canonicalCubeBeforePoisson_eq_all_modes
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
      canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f *
      ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
        (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
        ∑'h:O,actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
          (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
          (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
          (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
          W (fun _=>1) (fun _=>1) 1 1 K
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by sorry
