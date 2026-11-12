-- Prove2me | Theorems.Thm_OAI_CubicEisenstein_kernelCorrespondenceFunction_integral
-- name    : OAI.CubicEisenstein.kernelCorrespondenceFunction_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:14:33.756934+00:00
-- url     : https://prove2.me/theorems/208673a7-e39b-4739-a8a5-8c726376ea18
-- title:
--   Cubic Eisenstein: kernel Correspondence Function integral
-- statement:
--   The Cubic Eisenstein construction uses the kernel Correspondence Function integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CorrespondencePullback.lean#L146-L174
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CorrespondencePullback.lean#L146-L174

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondenceTests
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondencePullback
set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
include hHK

theorem OAI.CubicEisenstein.kernelCorrespondenceFunction_integral (f : KernelQuotient→ℂ) (hf : Measurable f)
    (hi : Integrable f (integralQuotientVolume globalKubotaKernel)) :
    (∫q,kernelCorrespondenceFunction hJK e g he f q∂integralQuotientVolume globalKubotaKernel)=
      (J.relIndex globalKubotaKernel:ℂ)*(∫q,f q∂integralQuotientVolume globalKubotaKernel) := by sorry
