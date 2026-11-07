-- Prove2me | Theorems.Thm_OAI_FiniteSFactor_outsideExpSum_empty_eq_normFiberExpSum
-- name    : OAI.FiniteSFactor.outsideExpSum_empty_eq_normFiberExpSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:42:46.365598+00:00
-- url     : https://prove2.me/theorems/c9752290-78ae-4e58-b4af-1a7a7f9d7aaf
-- title:
--   Finite SFactor: outside Exp Sum empty eq norm Fiber Exp Sum
-- statement:
--   The Finite SFactor construction uses the outside Exp Sum empty eq norm Fiber Exp Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/FiniteEulerFactors.lean#L214-L220
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/FiniteEulerFactors.lean#L214-L220

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

theorem OAI.FiniteSFactor.outsideExpSum_empty_eq_normFiberExpSum {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    outsideExpSum ∅ (ShortDraftHeckeBridge.baseChangeWeight χ) t =
      ShortDraftHeckeBridge.normFiberExpSum
        (ShortDraftHeckeBridge.baseChangeWeight χ) t := by sorry
