-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_annularHighEnergy_column_shells_small_power
-- name    : OAI.CanonicalQuadraticSieve.annularHighEnergy_column_shells_small_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:59:43.602039+00:00
-- url     : https://prove2.me/theorems/14fcbd1b-817e-421b-8a2e-921b8a8edf6c
-- title:
--   Canonical Quadratic Sieve: annular High Energy column shells small power
-- statement:
--   The Canonical Quadratic Sieve construction uses the annular High Energy column shells small power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/DyadicColumns.lean#L99-L112
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/DyadicColumns.lean#L99-L112

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConstantDirichletSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_DyadicColumns
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
open OAI.CanonicalQuadraticSieve

theorem OAI.CanonicalQuadraticSieve.annularHighEnergy_column_shells_small_power
    (ε : ℝ) (hε : 0 < ε) (M N K : ℝ) (hN : 1 ≤ N) (a : idealRange N → ℂ) :
    annularHighEnergy M N K a ≤ ((2 + 1 / (ε * Real.log 2)) * N ^ ε) *
      ∑ j : Fin (columnDyadicLength N + 1),
        annularHighEnergy M ((2 : ℝ) ^ j.val) K
          (coefficientAtScale N ((2 : ℝ) ^ j.val)
            (dyadicColumnCoefficient N (columnDyadicLength N) (columnDyadicLength_cover N) j a)) := by sorry
