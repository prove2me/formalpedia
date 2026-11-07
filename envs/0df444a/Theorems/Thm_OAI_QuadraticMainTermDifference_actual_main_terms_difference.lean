-- Prove2me | Theorems.Thm_OAI_QuadraticMainTermDifference_actual_main_terms_difference
-- name    : OAI.QuadraticMainTermDifference.actual_main_terms_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:40:00.452401+00:00
-- url     : https://prove2.me/theorems/05fa56da-2b22-4a77-b99a-b73ed4bafbb0
-- title:
--   Quadratic Main Term Difference: actual main terms difference
-- statement:
--   The Quadratic Main Term Difference construction uses the actual main terms difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/MainTermDifference.lean#L108-L151
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/MainTermDifference.lean#L108-L151

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeLabels
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_MainTermDifference
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
open scoped BigOperators Classical
open OAI.QuadraticMainTermDifference
open ActualEisensteinCubic QuadraticDivisorCancellation QuadraticMainBoundary

theorem OAI.QuadraticMainTermDifference.actual_main_terms_difference {ι κ : Type*} [DecidableEq κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
    (q : κ → O) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hprime : ∀ i, Prime (Ideal.span {q i}))
    (hinj : Function.Injective (fun i => (Ideal.span {q i} : Ideal O)))
    (T G : Finset κ) (hTG : Disjoint T G) (K : ℝ)
    (havoid : ∀ i ∈ G, ∀ j ∈ S, q i ∉ P j) :
    partialSquarefreeSum P hg S q K (T ∪ G) * divisorSum P hg S q G -
      partialSquarefreeSum P hg S q K T *
        (∏ i ∈ G, (1 - (1 : ℂ) / (Ideal.absNorm (Ideal.span {q i}) : ℂ))) =
      ∑ H ∈ T.powerset, ∑ D ∈ G.powerset, ∑ E ∈ G.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
        normalizedRow P hg S ((∏ i ∈ H, q i) * (∏ i ∈ D, q i) * ∏ i ∈ E, q i) *
        (cutoffDifference K (∏ i ∈ H, Ideal.span {q i})
          (∏ i ∈ D, Ideal.span {q i}) : ℝ) := by sorry
