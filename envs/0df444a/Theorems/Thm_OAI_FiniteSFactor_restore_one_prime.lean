-- Prove2me | Theorems.Thm_OAI_FiniteSFactor_restore_one_prime
-- name    : OAI.FiniteSFactor.restore_one_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:15:35.042586+00:00
-- url     : https://prove2.me/theorems/dbb68823-7d73-4d87-bdb1-441f7034db4e
-- title:
--   Finite SFactor: restore one prime
-- statement:
--   The Finite SFactor construction uses the restore one prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L216-L259
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L216-L259

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

theorem OAI.FiniteSFactor.restore_one_prime (P : Ideal O) (hP : Prime P)
    (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ J, ¬P ∣ J → w (P * J) = w P * w J)
    (m : ℕ) :
    (∑ I ∈ fiber (Ideal.absNorm P * m), w I) =
      exceptPrimeCoeff P w (Ideal.absNorm P * m) +
        w P * exceptPrimeCoeff P w m := by sorry
