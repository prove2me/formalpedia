-- Prove2me | Theorems.Thm_OAI_CubicEisenstein_compact_clm_closedBall
-- name    : OAI.CubicEisenstein.compact_clm_closedBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:54:03.253441+00:00
-- url     : https://prove2.me/theorems/7d1fb998-e79b-4fb0-8b5a-5be35f35e6e0
-- title:
--   Cubic Eisenstein: compact clm closed Ball
-- statement:
--   The Cubic Eisenstein construction uses the compact clm closed Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/RadialWindows.lean#L513-L516
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/RadialWindows.lean#L513-L516

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_PoissonSource
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RadialWindows
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
attribute [local instance] OAI.CubicEisenstein._p2m_local_instance_a77077472d_474
attribute [local instance] OAI.CubicEisenstein._p2m_local_instance_a77077472d_475

theorem OAI.CubicEisenstein.compact_clm_closedBall {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedSpace ℝ V] [NormedSpace ℝ W] (T : V →L[ℝ] W)
    (hT : IsCompactOperator T) (R : ℝ) : IsCompact (closure (T '' Metric.closedBall 0 R)) := by sorry
