-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_canonicalCubeSourcePair_factor
-- name    : OAI.SecondPassArithmetic.canonicalCubeSourcePair_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:24:20.475914+00:00
-- url     : https://prove2.me/theorems/436fa499-0ae0-4a9d-acd7-7d31b0b2bc71
-- title:
--   Second Pass Arithmetic: canonical Cube Source Pair factor
-- statement:
--   The Second Pass Arithmetic construction uses the canonical Cube Source Pair factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/PoissonSource.lean#L630-L659
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/PoissonSource.lean#L630-L659

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

theorem OAI.SecondPassArithmetic.canonicalCubeSourcePair_factor
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀i,lambda^2∣p i-1)
    (b : CubeCoordinates ι) (hb : b.Admissible) (C N P : Finset ι)
    (hCB : Disjoint C b.support) (hNC : Disjoint N C) (hPC : Disjoint P C)
    (hNB : Disjoint N b.support) (hPB : Disjoint P b.support) (hNP : Disjoint N P)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeSourcePair p hp hcop hg b.support ((b.rightDivisor∪C)∪N) ((b.leftDivisor∪C)∪P)
      b.leftExponent b.rightExponent Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
    canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
      (star (columnCoefficient p hp hcop hg N*canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁ N)*
        (columnCoefficient p hp hcop hg P*canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂ P))*
      ∑'z:O,rowCoprimeMask (fun i=>Ideal.span {p i})
        (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit) z*
        blockRow p hg ((N∪P)∪cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)
          (threeBlockExponent N P (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) z*
        W (‖eisEmbedding z‖^2/K) := by sorry
