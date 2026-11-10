-- Prove2me | Theorems.Thm_OAI_CubicEisenstein_kernelEuclideanProjection_integral
-- name    : OAI.CubicEisenstein.kernelEuclideanProjection_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:24:32.694301+00:00
-- url     : https://prove2.me/theorems/78f74114-8a6c-4666-b89b-e21d2c5e6418
-- title:
--   Cubic Eisenstein: kernel Euclidean Projection integral
-- statement:
--   The Cubic Eisenstein construction uses the kernel Euclidean Projection integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/LocalCutoffs.lean#L253-L262
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/LocalCutoffs.lean#L253-L262

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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff ENNReal

theorem OAI.CubicEisenstein.kernelEuclideanProjection_integral (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (g : KernelQuotient → ℝ)
    (hg : AEStronglyMeasurable g (integralQuotientVolume globalKubotaKernel)) :
    (∫p in S,g (kernelEuclideanProjection p)∂hyperbolicEuclideanVolume)=
      ∫q in kernelEuclideanProjection '' S,g q∂integralQuotientVolume globalKubotaKernel := by sorry
