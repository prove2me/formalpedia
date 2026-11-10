-- Prove2me | Theorems.Thm_OAI_CompletedGauss_completed_actual_fiber_cost
-- name    : OAI.CompletedGauss.completed_actual_fiber_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T13:53:08.754243+00:00
-- url     : https://prove2.me/theorems/2b654f5b-be4e-4e86-86d6-9fa032ac2bc9
-- title:
--   Completed Gauss: completed actual fiber cost
-- statement:
--   The Completed Gauss construction uses the completed actual fiber cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/ReflectedDyadicSeries.lean#L412-L445
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/ReflectedDyadicSeries.lean#L412-L445

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DyadicKernel
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_ReflectedDyadicSeries
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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.CompletedGauss
open ActualEisensteinCubic

theorem OAI.CompletedGauss.completed_actual_fiber_cost {ι : Type*} [Fintype ι]
    (deltaLoss K X : ℝ) (hδ : 0≤deltaLoss) (hK : 1≤K) (hX : 1≤X)
    (I F Q : Ideal O) (hI : I≠0) (hQ : Q≠0) (hIK : (Ideal.absNorm I:ℝ)≤K)
    (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) (e : ι→Fin 3) :
    let j := fun i => completedLocalExponent I F (P i)
    let k := K/((Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ))
    let D := (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)
    let S := (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)
    let E := (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)
    let y := k^2*(Ideal.absNorm (∏i,P i):ℝ)^2/(X*D*E^3)
    (k*y)^(2*deltaLoss)*(k+y)/(S*E)≤
      (K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
        (Ideal.absNorm (rowPowerfulPart I):ℝ) := by sorry
