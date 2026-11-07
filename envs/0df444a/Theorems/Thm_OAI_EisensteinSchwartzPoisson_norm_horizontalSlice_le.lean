-- Prove2me | Theorems.Thm_OAI_EisensteinSchwartzPoisson_norm_horizontalSlice_le
-- name    : OAI.EisensteinSchwartzPoisson.norm_horizontalSlice_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:52:16.827509+00:00
-- url     : https://prove2.me/theorems/57217e7a-1031-456e-a19c-649de96bffd1
-- title:
--   Eisenstein Schwartz Poisson: norm horizontal Slice le
-- statement:
--   The Eisenstein Schwartz Poisson construction uses the norm horizontal Slice le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SecondPoissonScale.lean#L769-L774
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SecondPoissonScale.lean#L769-L774

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

theorem OAI.EisensteinSchwartzPoisson.norm_horizontalSlice_le (F : SchwartzMap ℂ ℂ) (η ξ : ℝ) :
    ‖horizontalSlice F η ξ‖ ≤
      (planeDecayConstant F / (1 + η ^ 2)) * (1 + ξ ^ 2)⁻¹ := by sorry
