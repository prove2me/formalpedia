-- Prove2me | Theorems.Thm_OAI_CompactScaleBridge_realCompactOutsideSum_isBigO_of_fixedTestPrimeMS
-- name    : OAI.CompactScaleBridge.realCompactOutsideSum_isBigO_of_fixedTestPrimeMS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:45:29.717602+00:00
-- url     : https://prove2.me/theorems/29e8c987-4404-4c51-ac96-9bef79e1853c
-- title:
--   Compact Scale Bridge: real Compact Outside Sum is Big O of fixed Test Prime MS
-- statement:
--   The Compact Scale Bridge construction uses the real Compact Outside Sum is Big O of fixed Test Prime MS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/CompactScale.lean#L127-L146
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/CompactScale.lean#L127-L146

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
open OAI.CompactScaleBridge
open ConcretePrimeRowBridge ShortDraftHeckeBridge Filter Asymptotics

theorem OAI.CompactScaleBridge.realCompactOutsideSum_isBigO_of_fixedTestPrimeMS
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (LipC ε : ℝ) (m₀ : ℕ)
    (hL : 0 ≤ LipC)
    (hLip : ∀ x y : ℝ, ‖W x - W y‖ ≤ LipC * |x - y|)
    (hε : 0 ≤ ε) (hW : ∀ y : ℝ, ‖W y‖ ≤ 1)
    (hMS : ∀ m : ℕ, m₀ ≤ m → FixedTestPrimeMS χ S hSbad W m ε) :
    (realCompactOutsideSum χ S W) =O[atTop]
      (fun D : ℝ => D ^ ((23 / 24 : ℝ) + ε)) := by sorry
