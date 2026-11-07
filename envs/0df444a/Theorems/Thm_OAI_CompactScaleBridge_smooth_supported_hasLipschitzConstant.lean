-- Prove2me | Theorems.Thm_OAI_CompactScaleBridge_smooth_supported_hasLipschitzConstant
-- name    : OAI.CompactScaleBridge.smooth_supported_hasLipschitzConstant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:43:00.28149+00:00
-- url     : https://prove2.me/theorems/e97f4ade-488f-497b-acf9-572ab4ad3645
-- title:
--   Compact Scale Bridge: smooth supported has Lipschitz Constant
-- statement:
--   The Compact Scale Bridge construction uses the smooth supported has Lipschitz Constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/FiniteEulerFactors.lean#L577-L596
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/FiniteEulerFactors.lean#L577-L596

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
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
open ConcretePrimeRowBridge ShortDraftHeckeBridge

theorem OAI.CompactScaleBridge.smooth_supported_hasLipschitzConstant
    (W : ℝ → ℂ) (hSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hSupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0) :
    ∃ LipC : ℝ, 0 ≤ LipC ∧
      ∀ x y : ℝ, ‖W x - W y‖ ≤ LipC * |x - y| := by sorry
