-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_first_row_enlargement
-- name    : OAI.SecondPassArithmetic.first_row_enlargement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T09:50:04.50056+00:00
-- url     : https://prove2.me/theorems/a31c69f9-d8a5-4860-b7d4-2f0abf42bdfa
-- title:
--   Second Pass Arithmetic: first row enlargement
-- statement:
--   The Second Pass Arithmetic construction uses the first row enlargement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/LogarithmicBins.lean#L562-L600
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/LogarithmicBins.lean#L562-L600

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_LogarithmicBins
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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel dilationLabel jLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
include hp

theorem OAI.SecondPassArithmetic.first_row_enlargement (b : GlobalCubeBlock ι) (x : Ideal O × O)
    (K ell B F : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (hb₁ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B)
    (hf : (Ideal.absNorm x.1 : ℝ)≤F)
    (hh : ‖eisEmbedding x.2‖^2 ≤
      ell^2*primeProductNorm p (cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit)*
      primeProductNorm p b.firstDivisor/
      (K*‖eisEmbedding (aLabel p b.cube.support b.cube.leftBit)‖^2*
        ‖eisEmbedding (aLabel p b.cube.support b.cube.rightBit)‖^2*(primeProductNorm p b.common)^2)) :
    ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
        b.cube.leftBit b.cube.rightBit) x)‖^2 ≤
      globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by sorry
