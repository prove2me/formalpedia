-- Prove2me | Theorems.Thm_OAI_CubicEisenstein_cusp_hardy_halfline
-- name    : OAI.CubicEisenstein.cusp_hardy_halfline
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-08T19:46:09.805835+00:00
-- url     : https://prove2.me/theorems/938fd4d5-a0ad-4fc0-a902-87235e46a0ba
-- title:
--   Cubic Eisenstein: cusp hardy halfline
-- statement:
--   The Cubic Eisenstein construction uses the cusp hardy halfline property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CuspCoercivity.lean#L232-L243
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CuspCoercivity.lean#L232-L243

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PrincipalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
open OAI.CubicEisenstein

theorem OAI.CubicEisenstein.cusp_hardy_halfline (f : ℝ → ℂ) (a : ℝ) (ha : 0<a) (hfa : f a=0)
    (hf : ∀t∈Set.Ici a,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Ici a))
    (hM : IntegrableOn (fun t => ‖f t‖^2/t^3) (Set.Ioi a) volume)
    (hE : IntegrableOn (fun t => ‖deriv f t‖^2/t) (Set.Ioi a) volume) :
    (∫t in Set.Ioi a,‖f t‖^2/t^3)≤∫t in Set.Ioi a,‖deriv f t‖^2/t := by sorry
