-- Prove2me | Theorems.Thm_OAI_CompletedGauss_exceptional_normalized_bound
-- name    : OAI.CompletedGauss.exceptional_normalized_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:01:08.491781+00:00
-- url     : https://prove2.me/theorems/8645d23c-47f5-4404-8431-c0d7643f541d
-- title:
--   Completed Gauss: exceptional normalized bound
-- statement:
--   The Completed Gauss construction uses the exceptional normalized bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/RowCaps.lean#L339-L356
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/RowCaps.lean#L339-L356

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_PowerfulParts
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_LogarithmicBins
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowCaps
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
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets

theorem OAI.CompletedGauss.exceptional_normalized_bound {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hp : ∀i,P i≠0)
    (e : ι→Fin 3) (n b : O) (U B : ℝ) (hU : 0<U) (hB : 0<B) :
    ‖exceptionalBranch P e n b‖ /
      (Real.sqrt ((Ideal.absNorm (exceptionalDivisor P e 1):ℝ)*U)*
        ((Ideal.absNorm (exceptionalDivisor P e 2):ℝ)*B)) ≤
      1/(Real.sqrt U*B*Real.sqrt ((Ideal.absNorm (exceptionalDivisor P e 0):ℝ)*
        (Ideal.absNorm (exceptionalDivisor P e 2):ℝ))) := by sorry
