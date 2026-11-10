-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_improved_threshold_low
-- name    : OAI.CanonicalQuadraticSieve.improved_threshold_low
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T06:20:54.740008+00:00
-- url     : https://prove2.me/theorems/3c9cb892-fbd3-4a3b-9d6d-2e46dca4a126
-- title:
--   Canonical Quadratic Sieve: improved threshold low
-- statement:
--   The Canonical Quadratic Sieve construction uses the improved threshold low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/SelectedExponents.lean#L372-L389
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/SelectedExponents.lean#L372-L389

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonConstants
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
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
open scoped BigOperators Classical SchwartzMap
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise
open OAI.CanonicalQuadraticSieve

theorem OAI.CanonicalQuadraticSieve.improved_threshold_low (α C η N M : ℝ) (hα : 0<α) (hC : 0<C)
    (hN : 0<N) (hM0 : 0<M) (hM : N^(2-1/α)≤M) :
    (selectedPoissonK C M N η)^α≤C^α*(M*N)^(η*α)*N := by sorry
