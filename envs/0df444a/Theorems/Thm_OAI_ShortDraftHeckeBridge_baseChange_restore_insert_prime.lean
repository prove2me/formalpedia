-- Prove2me | Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChange_restore_insert_prime
-- name    : OAI.ShortDraftHeckeBridge.baseChange_restore_insert_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:15:34.663578+00:00
-- url     : https://prove2.me/theorems/46519e1d-cd20-4464-9b74-549c9ab05e7a
-- title:
--   Short Draft Hecke Bridge: base Change restore insert prime
-- statement:
--   The Short Draft Hecke Bridge construction uses the base Change restore insert prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L368-L380
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L368-L380

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
open OAI.ShortDraftHeckeBridge

theorem OAI.ShortDraftHeckeBridge.baseChange_restore_insert_prime {q : ℕ}
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPnot : P ∉ S) (n : ℕ) :
    FiniteSFactor.outsideCoeff S (baseChangeWeight χ) n =
      FiniteSFactor.outsideCoeff (insert P S) (baseChangeWeight χ) n +
      (if Ideal.absNorm P ∣ n then
        baseChangeWeight χ P *
          FiniteSFactor.outsideCoeff (insert P S) (baseChangeWeight χ)
            (n / Ideal.absNorm P) else 0) := by sorry
