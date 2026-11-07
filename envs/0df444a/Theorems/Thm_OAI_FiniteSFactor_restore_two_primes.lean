-- Prove2me | Theorems.Thm_OAI_FiniteSFactor_restore_two_primes
-- name    : OAI.FiniteSFactor.restore_two_primes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:16:02.918763+00:00
-- url     : https://prove2.me/theorems/f4ed2609-d91c-4189-82fe-b19ceb913de0
-- title:
--   Finite SFactor: restore two primes
-- statement:
--   The Finite SFactor construction uses the restore two primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L556-L585
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L556-L585

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
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
open OAI.FiniteSFactor

theorem OAI.FiniteSFactor.restore_two_primes (P Q : Ideal O) (hP : Prime P) (hQ : Prime Q)
    (hne : P ≠ Q) (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ I J, IsRelPrime I J → w (I * J) = w I * w J)
    (n : ℕ) :
    outsideCoeff ∅ w n =
      (outsideCoeff (insert Q {P}) w n +
        (if Ideal.absNorm Q ∣ n then
          w Q * outsideCoeff (insert Q {P}) w (n / Ideal.absNorm Q) else 0)) +
      (if Ideal.absNorm P ∣ n then
        w P *
          (outsideCoeff (insert Q {P}) w (n / Ideal.absNorm P) +
            (if Ideal.absNorm Q ∣ n / Ideal.absNorm P then
              w Q * outsideCoeff (insert Q {P}) w
                ((n / Ideal.absNorm P) / Ideal.absNorm Q) else 0))
        else 0) := by sorry
