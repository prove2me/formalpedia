-- Prove2me | Theorems.Thm_OAI_DescentWeightedCauchy_first_energy_pushforward
-- name    : OAI.DescentWeightedCauchy.first_energy_pushforward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:45:47.941612+00:00
-- url     : https://prove2.me/theorems/a690e63a-52fd-454d-b9fe-b25de26236f5
-- title:
--   Descent Weighted Cauchy: first energy pushforward
-- statement:
--   The Descent Weighted Cauchy construction uses the first energy pushforward property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ReflectedKernel.lean#L543-L555
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ReflectedKernel.lean#L543-L555

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_InitialBound
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ReflectedKernel
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
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
open scoped BigOperators Classical
open OAI.DescentWeightedCauchy

theorem OAI.DescentWeightedCauchy.first_energy_pushforward
    (s : Finset (Ideal O × Ideal O)) (t : Finset (Ideal O))
    (E : Ideal O) (w : Ideal O × Ideal O → ℂ) (P : Ideal O → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hmap : ∀ x ∈ s, firstRowMap E x ∈ t)
    (ht : ∀ Y ∈ t, Y ≠ ⊥) (hw : ∀ x ∈ s, ‖w x‖ ≤ C) :
    (∑ x ∈ s, ‖w x‖ * ‖P (firstRowMap E x)‖ ^ 2) ≤
      ∑ Y ∈ t, C * (IdealMobiusDivisorSum.idealDivisors Y).card * ‖P Y‖ ^ 2 := by sorry
