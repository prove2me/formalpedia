-- Prove2me | Theorems.Thm_OAI_FiniteSFactor_restore_one_prime_all
-- name    : OAI.FiniteSFactor.restore_one_prime_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:15:22.186757+00:00
-- url     : https://prove2.me/theorems/45e3206c-8d13-496d-9bcc-5ccac22416b7
-- title:
--   Finite SFactor: restore one prime all
-- statement:
--   The Finite SFactor construction uses the restore one prime all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L261-L288
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L261-L288

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

theorem OAI.FiniteSFactor.restore_one_prime_all (P : Ideal O) (hP : Prime P)
    (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ J, ¬P ∣ J → w (P * J) = w P * w J)
    (n : ℕ) :
    (∑ I ∈ fiber n, w I) = exceptPrimeCoeff P w n +
      (if Ideal.absNorm P ∣ n then
        w P * exceptPrimeCoeff P w (n / Ideal.absNorm P) else 0) := by sorry
