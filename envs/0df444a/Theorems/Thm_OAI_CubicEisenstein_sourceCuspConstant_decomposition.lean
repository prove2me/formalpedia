-- Prove2me | Theorems.Thm_OAI_CubicEisenstein_sourceCuspConstant_decomposition
-- name    : OAI.CubicEisenstein.sourceCuspConstant_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:20:44.388729+00:00
-- url     : https://prove2.me/theorems/5cb62f9d-46ca-4192-97cf-18359c3231e1
-- title:
--   Cubic Eisenstein: source Cusp Constant decomposition
-- statement:
--   The Cubic Eisenstein construction uses the source Cusp Constant decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Reciprocity/PrimaryCongruences.lean#L671-L675
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Reciprocity/PrimaryCongruences.lean#L671-L675

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_ResiduesModThree
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_PrimaryCongruences
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
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open OAI.CubicEisenstein
open ConcreteTraceCRT CubicKubota EisensteinCuspModThree
local notation "O" => ActualEisensteinCubic.O

theorem OAI.CubicEisenstein.sourceCuspConstant_decomposition (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo) (j : Fin 3)
    (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T) :
    sourceCuspConstant M=levelTwoComplexCharacter G*(if j=0 then sourcePrincipalCuspConstant else 0) := by sorry
