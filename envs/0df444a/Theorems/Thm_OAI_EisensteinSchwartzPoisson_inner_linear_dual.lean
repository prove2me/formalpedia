-- Prove2me | Theorems.Thm_OAI_EisensteinSchwartzPoisson_inner_linear_dual
-- name    : OAI.EisensteinSchwartzPoisson.inner_linear_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:56:53.475319+00:00
-- url     : https://prove2.me/theorems/1d77224e-29ac-4df2-bbf5-24966be54dd0
-- title:
--   Eisenstein Schwartz Poisson: inner linear dual
-- statement:
--   The Eisenstein Schwartz Poisson construction uses the inner linear dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/EisensteinLattice.lean#L79-L82
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/EisensteinLattice.lean#L79-L82

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_EisensteinLattice
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
open OAI.EisensteinSchwartzPoisson
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem OAI.EisensteinSchwartzPoisson.inner_linear_dual (A : ℂ ≃L[ℝ] ℂ) (x y : ℂ) :
    inner ℝ (A x) (dualMap A y) = inner ℝ x y := by sorry
