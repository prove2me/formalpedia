-- Prove2me | Theorems.Thm_OAI_FiniteSFactor_outsideLSeries_finiteEuler_baseChange
-- name    : OAI.FiniteSFactor.outsideLSeries_finiteEuler_baseChange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:42:52.734667+00:00
-- url     : https://prove2.me/theorems/ddbbed35-ec48-4759-92ea-3d20ea91609a
-- title:
--   Finite SFactor: outside LSeries finite Euler base Change
-- statement:
--   The Finite SFactor construction uses the outside LSeries finite Euler base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/FiniteEulerFactors.lean#L351-L386
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/FiniteEulerFactors.lean#L351-L386

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

theorem OAI.FiniteSFactor.outsideLSeries_finiteEuler_baseChange {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P)
    (s : ℂ) (hs : 2 < s.re) :
    LSeries (outsideCoeff ∅ (ShortDraftHeckeBridge.baseChangeWeight χ)) s =
      (∏ P ∈ S, (1 + ShortDraftHeckeBridge.baseChangeWeight χ P *
        (Ideal.absNorm P : ℂ) ^ (-s))) *
      LSeries (outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)) s := by sorry
