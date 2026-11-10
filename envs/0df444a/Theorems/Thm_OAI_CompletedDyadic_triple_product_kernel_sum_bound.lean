-- Prove2me | Theorems.Thm_OAI_CompletedDyadic_triple_product_kernel_sum_bound
-- name    : OAI.CompletedDyadic.triple_product_kernel_sum_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:52:03.491205+00:00
-- url     : https://prove2.me/theorems/13b7445a-33a5-4fd9-a2ae-0c2e9f32acda
-- title:
--   Completed Dyadic: triple product kernel sum bound
-- statement:
--   The Completed Dyadic construction uses the triple product kernel sum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/DyadicKernel.lean#L405-L431
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/DyadicKernel.lean#L405-L431

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_PoissonSource
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_QuantitativePassage
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DyadicKernel
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
open scoped BigOperators
open OAI.CompletedDyadic

theorem OAI.CompletedDyadic.triple_product_kernel_sum_bound (s A β ρ q : ℝ)
    (hs : 0<s) (hsA : s<A) (hβ : β<3*s) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀t : ℝ,0<t → Summable (tripleTerm t s A β ρ q) ∧
      (∑'i : ℕ×ℕ×ℕ,tripleTerm t s A β ρ q i)≤C*t^(-s) := by sorry
