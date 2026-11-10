-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_orientedCubeFirstBlock_single_source
-- name    : OAI.SecondPassArithmetic.orientedCubeFirstBlock_single_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:21:16.698823+00:00
-- url     : https://prove2.me/theorems/9e47898a-4000-4e88-82a1-f9a19b994ab6
-- title:
--   Second Pass Arithmetic: oriented Cube First Block single source
-- statement:
--   The Second Pass Arithmetic construction uses the oriented Cube First Block single source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/HarmonicAggregation.lean#L177-L202
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/HarmonicAggregation.lean#L177-L202

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_BranchScaling
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RadialWindows
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HarmonicAggregation
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic FirstPassCubeLabels
open ConcretePrimeRowBridge (idealGenerator)
variable {ι:Type*} [DecidableEq ι]
  (p:ι→OAI.SecondPassArithmetic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

theorem OAI.SecondPassArithmetic.orientedCubeFirstBlock_single_source
    (pool:Finset ι) (b:CubeCoordinates ι) (C D:Finset ι) (I:Ideal O) (h:O)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) :
    orientedCubeFirstBlock p hp hcop hg pool (sourceGlobalBlock b C D) {(I,h)} (fun _=>1)
      Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell =
    (primeProductNorm p D:ℂ)⁻¹ *
      actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (originalLabelColumn p hg b.support b.leftBit b.rightBit true
          (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p
            (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)) S)))
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) C) (idealGenerator I))
        (originalLabelColumn p hg b.support b.leftBit b.rightBit false
          (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p
            (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) S)))
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) C) (idealGenerator I))
        W V₁ V₂ (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))
          (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) K
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by sorry
