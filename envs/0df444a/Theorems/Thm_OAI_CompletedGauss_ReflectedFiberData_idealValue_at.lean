-- Prove2me | Theorems.Thm_OAI_CompletedGauss_ReflectedFiberData_idealValue_at
-- name    : OAI.CompletedGauss.ReflectedFiberData.idealValue_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:26:52.433812+00:00
-- url     : https://prove2.me/theorems/89025c2a-3442-460f-9f87-94e4bd11c2f3
-- title:
--   Reflected Fiber Data: ideal Value at
-- statement:
--   The Reflected Fiber Data construction uses the ideal Value at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/LocalCutoffs.lean#L578-L581
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/LocalCutoffs.lean#L578-L581

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_BranchScaling
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs
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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve
open ActualEisensteinCubic CanonicalQuadraticSieve
open OAI.CompletedGauss.ReflectedFiberData

theorem OAI.CompletedGauss.ReflectedFiberData.idealValue_at {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (J : idealRange (completedResidualScale K I Q)) :
    d.idealValue W X ρ q J.val=d.value W X ρ q J := by sorry
