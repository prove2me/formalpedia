-- Prove2me | Theorems.Thm_OAI_CompactScaleBridge_realCompactOutsideSum_eq_outsideCompactSum
-- name    : OAI.CompactScaleBridge.realCompactOutsideSum_eq_outsideCompactSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:05.494197+00:00
-- url     : https://prove2.me/theorems/3eaae1fb-17a5-431b-9972-042ed248e089
-- title:
--   Compact Scale Bridge: real Compact Outside Sum eq outside Compact Sum
-- statement:
--   The Compact Scale Bridge construction uses the real Compact Outside Sum eq outside Compact Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/CompactWeights.lean#L118-L126
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/CompactWeights.lean#L118-L126

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
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
open OAI.CompactScaleBridge
open ConcretePrimeRowBridge ShortDraftHeckeBridge Filter Asymptotics

theorem OAI.CompactScaleBridge.realCompactOutsideSum_eq_outsideCompactSum
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (W : ℝ → ℂ) (D : ℝ)
    (hD : 0 < D) (hSupp : ∀ y : ℝ, 2 ≤ y → W y = 0) :
    realCompactOutsideSum χ S W D =
      CompactMellinBridge.outsideCompactSum χ S W D⁻¹ := by sorry
