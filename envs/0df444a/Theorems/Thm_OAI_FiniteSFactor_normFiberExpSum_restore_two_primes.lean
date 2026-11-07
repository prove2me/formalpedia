-- Prove2me | Theorems.Thm_OAI_FiniteSFactor_normFiberExpSum_restore_two_primes
-- name    : OAI.FiniteSFactor.normFiberExpSum_restore_two_primes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:43:21.399493+00:00
-- url     : https://prove2.me/theorems/01829225-b0a7-4fc5-b4af-ab7a1581f65b
-- title:
--   Finite SFactor: norm Fiber Exp Sum restore two primes
-- statement:
--   The Finite SFactor construction uses the norm Fiber Exp Sum restore two primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/FiniteEulerFactors.lean#L222-L268
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/FiniteEulerFactors.lean#L222-L268

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

theorem OAI.FiniteSFactor.normFiberExpSum_restore_two_primes {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (P Q : Ideal O) (hP : Prime P) (hQ : Prime Q) (hPQ : P ≠ Q)
    (t : ℝ) (ht : 0 < t) :
    ShortDraftHeckeBridge.normFiberExpSum
      (ShortDraftHeckeBridge.baseChangeWeight χ) t =
        outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ) t +
        ShortDraftHeckeBridge.baseChangeWeight χ Q *
          outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm Q : ℝ) * t) +
        ShortDraftHeckeBridge.baseChangeWeight χ P *
          outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm P : ℝ) * t) +
        ShortDraftHeckeBridge.baseChangeWeight χ P *
          ShortDraftHeckeBridge.baseChangeWeight χ Q *
          outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm Q : ℝ) * ((Ideal.absNorm P : ℝ) * t)) := by sorry
