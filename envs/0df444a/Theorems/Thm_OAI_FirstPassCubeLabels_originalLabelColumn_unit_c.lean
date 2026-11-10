-- Prove2me | Theorems.Thm_OAI_FirstPassCubeLabels_originalLabelColumn_unit_c
-- name    : OAI.FirstPassCubeLabels.originalLabelColumn_unit_c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T15:19:33.673141+00:00
-- url     : https://prove2.me/theorems/19781637-ad02-4405-a3ab-9a7526620930
-- title:
--   First Pass Cube Labels: original Label Column unit c
-- statement:
--   The First Pass Cube Labels construction uses the original Label Column unit c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/BranchScaling.lean#L432-L438
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/BranchScaling.lean#L432-L438

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_ReflectedDyadicSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_BranchScaling
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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.FirstPassCubeLabels.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
omit [DecidableEq ι]

theorem OAI.FirstPassCubeLabels.originalLabelColumn_unit_c (B : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (C : Finset ι→ℂ) (u c f : O) (S : Finset ι) :
    originalLabelColumn p hg B ε₁ ε₂ negative C (u*c) f S =
      originalLabelColumn p hg B ε₁ ε₂ negative C c f S*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S u^4 := by sorry
