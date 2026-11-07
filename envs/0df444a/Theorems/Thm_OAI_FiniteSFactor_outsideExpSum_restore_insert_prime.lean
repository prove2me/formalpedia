-- Prove2me | Theorems.Thm_OAI_FiniteSFactor_outsideExpSum_restore_insert_prime
-- name    : OAI.FiniteSFactor.outsideExpSum_restore_insert_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:19:14.790193+00:00
-- url     : https://prove2.me/theorems/3584a087-ec74-43cb-a29d-dcccad9ba869
-- title:
--   Finite SFactor: outside Exp Sum restore insert prime
-- statement:
--   The Finite SFactor construction uses the outside Exp Sum restore insert prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/FiniteEulerRestoration.lean#L181-L205
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/FiniteEulerRestoration.lean#L181-L205

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
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
open OAI.FiniteSFactor

theorem OAI.FiniteSFactor.outsideExpSum_restore_insert_prime
    (S : Finset (Ideal O)) (hprime : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPnot : P ∉ S)
    (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ I J, IsRelPrime I J → w (I * J) = w I * w J)
    (t : ℝ)
    (hbase : Summable (fun n : ℕ =>
      outsideCoeff (insert P S) w n * Real.exp (-(n : ℝ) * t)))
    (hscaled : Summable (fun n : ℕ =>
      outsideCoeff (insert P S) w n *
        Real.exp (-(n : ℝ) * ((Ideal.absNorm P : ℝ) * t)))) :
    outsideExpSum S w t = outsideExpSum (insert P S) w t +
      w P * outsideExpSum (insert P S) w ((Ideal.absNorm P : ℝ) * t) := by sorry
