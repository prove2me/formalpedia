-- Prove2me | Theorems.Thm_OAI_CompactMellinBridge_outsideCompactSum_hasSum
-- name    : OAI.CompactMellinBridge.outsideCompactSum_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:45:24.547314+00:00
-- url     : https://prove2.me/theorems/0b75c340-339b-4fcb-b0fd-99f8ede9ce21
-- title:
--   Compact Mellin Bridge: outside Compact Sum has Sum
-- statement:
--   The Compact Mellin Bridge construction uses the outside Compact Sum has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/CompactScale.lean#L540-L562
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/CompactScale.lean#L540-L562

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
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
open OAI.CompactMellinBridge

theorem OAI.CompactMellinBridge.outsideCompactSum_hasSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal FiniteSFactor.O)) (W : ℝ → ℂ)
    (hsupp : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ =>
      FiniteSFactor.outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n *
        W ((n : ℝ) * t)) (outsideCompactSum χ S W t) := by sorry
