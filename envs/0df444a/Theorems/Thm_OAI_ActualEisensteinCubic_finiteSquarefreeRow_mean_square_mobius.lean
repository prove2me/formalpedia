-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_mean_square_mobius
-- name    : OAI.ActualEisensteinCubic.finiteSquarefreeRow_mean_square_mobius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:47:41.878013+00:00
-- url     : https://prove2.me/theorems/842b0834-173f-4c71-a6fc-24ad8cb265de
-- title:
--   Actual Eisenstein Cubic: finite Squarefree Row mean square mobius
-- statement:
--   The Actual Eisenstein Cubic construction uses the finite Squarefree Row mean square mobius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SecondPoissonScale.lean#L348-L367
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SecondPoissonScale.lean#L348-L367

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
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
open OAI.ActualEisensteinCubic

theorem OAI.ActualEisensteinCubic.finiteSquarefreeRow_mean_square_mobius
    {ι β : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1 ∉ P i)
    (C : Finset β) (support : β → Finset ι) (a : β → ℂ)
    (R : Finset O) (V : O → ℂ) :
    (∑ u ∈ R, V u * (↑(‖∑ n ∈ C,
      a n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) : ℂ)) =
      ∑ n ∈ C, ∑ m ∈ C, star (a n) * a m *
        ∑ E ∈ (support n ∩ support m).powerset, (-1 : ℂ) ^ E.card *
          ∑ u ∈ R.filter (fun u => ∀ i ∈ E, u ∈ P i),
            V u * star (finiteSquarefreeRow P hgood (support n \ support m) u) *
              finiteSquarefreeRow P hgood (support m \ support n) u := by sorry
