-- Prove2me | Theorems.Thm_OAI_GeneralPrimitiveTrace_in_coordinate_lattice_of_two_phases
-- name    : OAI.GeneralPrimitiveTrace.in_coordinate_lattice_of_two_phases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:05:26.825519+00:00
-- url     : https://prove2.me/theorems/436327b7-c129-4aa9-84e2-26ba8bab9e44
-- title:
--   General Primitive Trace: in coordinate lattice of two phases
-- statement:
--   The General Primitive Trace construction uses the in coordinate lattice of two phases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/IdealGenerators.lean#L366-L381
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/IdealGenerators.lean#L366-L381

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
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
open OAI.GeneralPrimitiveTrace
open Complex EisensteinEmbedding ConcreteTraceCRT
open scoped ComplexConjugate

theorem OAI.GeneralPrimitiveTrace.in_coordinate_lattice_of_two_phases (z : ℂ)
    (hz : ShortDraftTrace.breveE (z / eisLam) = 1)
    (hwz : ShortDraftTrace.breveE (omega3 * z / eisLam) = 1) :
    z ∈ coordinateSubring := by sorry
