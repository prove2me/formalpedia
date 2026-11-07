-- Prove2me | Theorems.Thm_OAI_CompactScaleBridge_real_to_integer_compact_bound
-- name    : OAI.CompactScaleBridge.real_to_integer_compact_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:42:56.535561+00:00
-- url     : https://prove2.me/theorems/2c197e66-b66e-4042-8107-e842753abcb5
-- title:
--   Compact Scale Bridge: real to integer compact bound
-- statement:
--   The Compact Scale Bridge construction uses the real to integer compact bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/FiniteEulerFactors.lean#L486-L575
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/FiniteEulerFactors.lean#L486-L575

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

theorem OAI.CompactScaleBridge.real_to_integer_compact_bound
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (W : ℝ → ℂ)
    (LipC D : ℝ) (m : ℕ)
    (hL : 0 ≤ LipC) (hLip : ∀ x y : ℝ, ‖W x - W y‖ ≤ LipC * |x - y|)
    (hD : 1 ≤ D) (hmLower : D ≤ (m : ℝ))
    (hmUpper : (m : ℝ) ≤ D + 1) :
    ‖(∑ I ∈ outsideIdealsUpTo S (2 * m),
        baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)) -
      (∑ I ∈ outsideIdealsUpTo S (2 * m),
        baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ)))‖ ≤
      640 * LipC := by sorry
