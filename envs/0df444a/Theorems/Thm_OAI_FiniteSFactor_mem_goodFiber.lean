-- Prove2me | Theorems.Thm_OAI_FiniteSFactor_mem_goodFiber
-- name    : OAI.FiniteSFactor.mem_goodFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:15:23.539966+00:00
-- url     : https://prove2.me/theorems/c971b8c7-5077-4835-a01c-8ccaa2dcdc6d
-- title:
--   Finite SFactor: mem good Fiber
-- statement:
--   The Finite SFactor construction uses the mem good Fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L135-L138
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L135-L138

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

theorem OAI.FiniteSFactor.mem_goodFiber {P : Ideal O} {m : ℕ} {J : Ideal O} :
    J ∈ goodFiber P m ↔ Ideal.absNorm J = m ∧ Squarefree J ∧ ¬P ∣ J := by sorry
