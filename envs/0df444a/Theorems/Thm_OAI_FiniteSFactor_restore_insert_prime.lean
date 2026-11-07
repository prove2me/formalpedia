-- Prove2me | Theorems.Thm_OAI_FiniteSFactor_restore_insert_prime
-- name    : OAI.FiniteSFactor.restore_insert_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:15:29.750201+00:00
-- url     : https://prove2.me/theorems/c716deb2-05fb-4228-bbf2-fbbe92212c0a
-- title:
--   Finite SFactor: restore insert prime
-- statement:
--   The Finite SFactor construction uses the restore insert prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L329-L350
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L329-L350

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
open OAI.FiniteSFactor
open scoped Classical
open scoped Classical

theorem OAI.FiniteSFactor.restore_insert_prime (S : Finset (Ideal O))
    (hprime : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P)
    (hPnot : P ∉ S) (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ I J, IsRelPrime I J → w (I * J) = w I * w J)
    (n : ℕ) :
    outsideCoeff S w n = outsideCoeff (insert P S) w n +
      (if Ideal.absNorm P ∣ n then
        w P * outsideCoeff (insert P S) w (n / Ideal.absNorm P) else 0) := by sorry
