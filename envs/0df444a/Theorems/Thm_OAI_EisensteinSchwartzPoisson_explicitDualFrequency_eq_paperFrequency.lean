-- Prove2me | Theorems.Thm_OAI_EisensteinSchwartzPoisson_explicitDualFrequency_eq_paperFrequency
-- name    : OAI.EisensteinSchwartzPoisson.explicitDualFrequency_eq_paperFrequency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:02:02.389312+00:00
-- url     : https://prove2.me/theorems/18341564-217f-45e4-a4ef-35b07af91718
-- title:
--   Eisenstein Schwartz Poisson: explicit Dual Frequency eq paper Frequency
-- statement:
--   The Eisenstein Schwartz Poisson construction uses the explicit Dual Frequency eq paper Frequency property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticRadialPoisson.lean#L267-L281
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/SexticRadialPoisson.lean#L267-L281

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_EisensteinLattice
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
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
open OAI.EisensteinSchwartzPoisson
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem OAI.EisensteinSchwartzPoisson.explicitDualFrequency_eq_paperFrequency (c : ℂ) (p : ℤ × ℤ) :
    explicitDualFrequency c p = paperFrequency (eisEmbedding (dualFrequencyEquiv p) / c) := by sorry
