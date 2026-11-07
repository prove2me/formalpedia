-- Prove2me | Theorems.Thm_OAI_FiniteSFactor_outsideExpSum_restore_baseChange
-- name    : OAI.FiniteSFactor.outsideExpSum_restore_baseChange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:42:49.147869+00:00
-- url     : https://prove2.me/theorems/103fbf8c-4b5b-4550-af9d-4bd6c266914d
-- title:
--   Finite SFactor: outside Exp Sum restore base Change
-- statement:
--   The Finite SFactor construction uses the outside Exp Sum restore base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/FiniteEulerFactors.lean#L193-L212
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/FiniteEulerFactors.lean#L193-L212

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
open OAI.FiniteSFactor

theorem OAI.FiniteSFactor.outsideExpSum_restore_baseChange {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPnot : P ∉ S)
    (t : ℝ) (ht : 0 < t) :
    outsideExpSum S (ShortDraftHeckeBridge.baseChangeWeight χ) t =
      outsideExpSum (insert P S) (ShortDraftHeckeBridge.baseChangeWeight χ) t +
        ShortDraftHeckeBridge.baseChangeWeight χ P *
          outsideExpSum (insert P S) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm P : ℝ) * t) := by sorry
