-- Prove2me | Theorems.Thm_OAI_CubicEisenstein_sourceCusp_average_enlarged_affine
-- name    : OAI.CubicEisenstein.sourceCusp_average_enlarged_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:35:42.131819+00:00
-- url     : https://prove2.me/theorems/44424cdf-f83a-43ef-a754-26dc7afaf82e
-- title:
--   Cubic Eisenstein: source Cusp average enlarged affine
-- statement:
--   The Cubic Eisenstein construction uses the source Cusp average enlarged affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CubeCuspAverage.lean#L83-L91
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CubeCuspAverage.lean#L83-L91

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CoverTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeCuspAverage
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
open scoped BigOperators Classical
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

theorem OAI.CubicEisenstein.sourceCusp_average_enlarged_affine (M : SL(2,ActualEisensteinCubic.O)) (b : ActualEisensteinCubic.O) (hb : b≠0)
    (c : ℂ) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding b*z+c)) v hv))=
      sourceCuspConstant M*(v:ℂ)^(2/3:ℂ) := by sorry
