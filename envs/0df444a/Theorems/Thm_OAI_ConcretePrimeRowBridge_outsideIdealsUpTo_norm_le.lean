-- Prove2me | Theorems.Thm_OAI_ConcretePrimeRowBridge_outsideIdealsUpTo_norm_le
-- name    : OAI.ConcretePrimeRowBridge.outsideIdealsUpTo_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:18:46.045733+00:00
-- url     : https://prove2.me/theorems/4930811e-fc93-4626-afef-009bc4aa05f8
-- title:
--   Concrete Prime Row Bridge: outside Ideals Up To norm le
-- statement:
--   The Concrete Prime Row Bridge construction uses the outside Ideals Up To norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/NormFiberExtraction.lean#L435-L438
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/NormFiberExtraction.lean#L435-L438

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
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
open OAI.ConcretePrimeRowBridge
open ShortDraftHeckeBridge FiniteSFactor

theorem OAI.ConcretePrimeRowBridge.outsideIdealsUpTo_norm_le (S : Finset (Ideal O)) (D : ℕ)
    (I : Ideal O) (hI : I ∈ outsideIdealsUpTo S D) :
    Ideal.absNorm I ≤ D := by sorry
