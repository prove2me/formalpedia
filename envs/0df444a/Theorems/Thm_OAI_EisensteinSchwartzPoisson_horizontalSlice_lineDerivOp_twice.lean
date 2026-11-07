-- Prove2me | Theorems.Thm_OAI_EisensteinSchwartzPoisson_horizontalSlice_lineDerivOp_twice
-- name    : OAI.EisensteinSchwartzPoisson.horizontalSlice_lineDerivOp_twice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:52:12.507288+00:00
-- url     : https://prove2.me/theorems/ab470cd0-32c6-40f3-8f3e-be36c4d54238
-- title:
--   Eisenstein Schwartz Poisson: horizontal Slice line Deriv Op twice
-- statement:
--   The Eisenstein Schwartz Poisson construction uses the horizontal Slice line Deriv Op twice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SecondPoissonScale.lean#L698-L701
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SecondPoissonScale.lean#L698-L701

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
open OAI.EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace

theorem OAI.EisensteinSchwartzPoisson.horizontalSlice_lineDerivOp_twice (F : SchwartzMap ℂ ℂ) (η : ℝ) :
    ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (horizontalSlice F η)) =
      horizontalSlice (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) η := by sorry
