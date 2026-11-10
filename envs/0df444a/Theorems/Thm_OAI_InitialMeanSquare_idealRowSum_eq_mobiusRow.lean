-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_idealRowSum_eq_mobiusRow
-- name    : OAI.InitialMeanSquare.idealRowSum_eq_mobiusRow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T09:32:47.486286+00:00
-- url     : https://prove2.me/theorems/38543222-41c5-41ff-a555-ac1e01163253
-- title:
--   Initial Mean Square: ideal Row Sum eq mobius Row
-- statement:
--   The Initial Mean Square construction uses the ideal Row Sum eq mobius Row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/SourceTransfer.lean#L483-L513
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/SourceTransfer.lean#L483-L513

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceTransfer
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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open OAI.InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CompletedGauss FirstCauchyArithmetic ShortDraftHeckeBridge

theorem OAI.InitialMeanSquare.idealRowSum_eq_mobiusRow (F : Finset (Ideal O)) (hF : ∀I∈F,Admissible I)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ) (z : O) :
    let hFpos := fun I hI => (hF I hI).1
    let hFgood := fun I hI P hP => ((hF I hI).2.2 P hP).1
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    idealRowSum F hFpos hFgood χ W z=
      mobiusRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ (normCharacter χ) 1
        (selectedIdealTest F W) z := by sorry
