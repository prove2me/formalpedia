-- Prove2me | Theorems.Thm_OAI_NormFiberCRT_ideal_eq_factors
-- name    : OAI.NormFiberCRT.ideal_eq_factors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:12:54.692218+00:00
-- url     : https://prove2.me/theorems/4b1fc67a-1a55-49e3-8922-16bb601902c3
-- title:
--   Norm Fiber CRT: ideal eq factors
-- statement:
--   The Norm Fiber CRT construction uses the ideal eq factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/LocalEulerIdentities.lean#L206-L232
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/LocalEulerIdentities.lean#L206-L232

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
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
open OAI.NormFiberCRT

theorem OAI.NormFiberCRT.ideal_eq_factors (I : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m * n) :
    I = (I ⊔ Ideal.span {(m : O)}) * (I ⊔ Ideal.span {(n : O)}) := by sorry
