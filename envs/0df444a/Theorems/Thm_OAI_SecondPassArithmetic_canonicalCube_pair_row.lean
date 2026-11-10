-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_canonicalCube_pair_row
-- name    : OAI.SecondPassArithmetic.canonicalCube_pair_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:24:19.336683+00:00
-- url     : https://prove2.me/theorems/ba39c051-c254-454a-858f-29a9a89b34c3
-- title:
--   Second Pass Arithmetic: canonical Cube pair row
-- statement:
--   The Second Pass Arithmetic construction uses the canonical Cube pair row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/PoissonSource.lean#L329-L373
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/PoissonSource.lean#L329-L373

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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient)
open FirstPassCubeLabels
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

theorem OAI.SecondPassArithmetic.canonicalCube_pair_row
    (B C N P : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hcover : ∀ i∈B,0<v₁ i+v₂ i)
    (hCB : Disjoint C B) (hNC : Disjoint N C) (hPC : Disjoint P C)
    (hNB : Disjoint N B) (hPB : Disjoint P B) (hNP : Disjoint N P)
    (z : O) :
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg
      (((B.filter fun i => ε₂ i)∪C)∪N) z) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg
        (((B.filter fun i => ε₁ i)∪C)∪P) z *
      star (multiplicityRow (fun i => Ideal.span {p i}) hg B v₂ z^3) *
      multiplicityRow (fun i => Ideal.span {p i}) hg B v₁ z^3 =
    rowCoprimeMask (fun i => Ideal.span {p i})
      (C∪cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z *
    blockRow p hg ((N∪P)∪cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂)
      (threeBlockExponent N P (fun i => v₁ i+v₂ i) ε₁ ε₂) z := by sorry
