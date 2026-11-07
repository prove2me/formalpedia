-- Prove2me | Theorems.Thm_OAI_NormFiberCRT_ideal_factor_norms
-- name    : OAI.NormFiberCRT.ideal_factor_norms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:12:59.477363+00:00
-- url     : https://prove2.me/theorems/d4d90ea6-a127-4956-a0bc-402860cc2a02
-- title:
--   Norm Fiber CRT: ideal factor norms
-- statement:
--   The Norm Fiber CRT construction uses the ideal factor norms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/LocalEulerIdentities.lean#L234-L250
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/LocalEulerIdentities.lean#L234-L250

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

theorem OAI.NormFiberCRT.ideal_factor_norms (I : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m * n) :
    Ideal.absNorm (I ⊔ Ideal.span {(m : O)}) = m ∧
      Ideal.absNorm (I ⊔ Ideal.span {(n : O)}) = n := by sorry
