-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_annularRayGcdBlock_eq_tsum
-- name    : OAI.CanonicalQuadraticSieve.annularRayGcdBlock_eq_tsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:33:27.358275+00:00
-- url     : https://prove2.me/theorems/86fa3d21-aa75-41a6-91cf-71a5e807446a
-- title:
--   Canonical Quadratic Sieve: annular Ray Gcd Block eq tsum
-- statement:
--   The Canonical Quadratic Sieve construction uses the annular Ray Gcd Block eq tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/AnnularRecursion.lean#L534-L558
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/AnnularRecursion.lean#L534-L558

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GcdReduction
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularRecursion
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
open scoped BigOperators Classical
open scoped SchwartzMap ContDiff
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction
open QuadraticSquarefreeKernel

theorem OAI.CanonicalQuadraticSieve.annularRayGcdBlock_eq_tsum (M N K : ℝ) (hM : 0 < M)
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑' I : Ideal O, if Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) then
        QuadraticInitialBound.annularSieveCutoff ((Ideal.absNorm I : ℝ) / M) * rayPairValue N D c a I else 0 := by sorry
