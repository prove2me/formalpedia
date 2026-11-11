-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_globalRetained_canonical_geometry
-- name    : OAI.SecondPassArithmetic.globalRetained_canonical_geometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:07:10.130509+00:00
-- url     : https://prove2.me/theorems/ee6d79aa-6e2a-49fc-85b0-58dd5ab31b06
-- title:
--   Second Pass Arithmetic: global Retained canonical geometry
-- statement:
--   The Second Pass Arithmetic construction uses the global Retained canonical geometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/CanonicalTailBounds.lean#L590-L639
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/CanonicalTailBounds.lean#L590-L639

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_RetainedDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalTailBounds
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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
include hp

theorem OAI.SecondPassArithmetic.globalRetained_canonical_geometry
    (source:Finset (GlobalSecondData ι)) (side:Bool) (q:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O) (j:GlobalLogIndex)
    (hq:q∈globalBinTriples p source side j)
    (Z η Ksrc K ell B F:ℝ) (m:ActualEisensteinCubic.O)
    (hZ:1<Z) (hη:η≤(1:ℝ)/1000) (hKsrc:0<Ksrc) (hK:0<K) (hKle:K≤Ksrc)
    (hell:0<ell) (hB:0<B) (hF:1≤F) (hprogress:Z^((1:ℝ)/1000)≤B*F)
    (hlarge:Real.exp 4≤B*F) (hstart:Ksrc≤Z^3)
    (hk:∀x∈source,x.source.frequency≠0)
    (hb₁:∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B)
    (hb₂:∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B)
    (hretained:globalBinRadial ell (globalPooledRowScale K ell B F j) j≤Z^η):
    let X:=globalPooledColumnScale ell j
    let lengthScale:=globalPooledLabelScale j
    let Kchild:=globalLogRep j 8*Real.exp 1
    0<X ∧ 1≤lengthScale ∧ 1≤Kchild ∧ X*lengthScale≤(ell*B^3)*F ∧
      Kchild≤Ksrc/Z^((1:ℝ)/1000) ∧ fixedDepthRank Z Kchild+1≤fixedDepthRank Z Ksrc ∧
      fixedDepthRank Z Ksrc≤3000 ∧ Kchild*‖eisEmbedding (fixedTripleMask m q)‖^2/(X*lengthScale)≤
        Z^η*(K*‖eisEmbedding m‖^2/((ell*B^3)*F)) ∧
      (∀z∈globalArithmeticTargets p source side q j,
        Squarefree z.1 ∧ z.2≠0 ∧ (Ideal.absNorm z.1:ℝ)≤lengthScale ∧ ‖eisEmbedding z.2‖^2≤Kchild) := by sorry
