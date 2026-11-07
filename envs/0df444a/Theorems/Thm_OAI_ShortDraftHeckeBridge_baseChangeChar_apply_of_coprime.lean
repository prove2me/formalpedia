-- Prove2me | Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChangeChar_apply_of_coprime
-- name    : OAI.ShortDraftHeckeBridge.baseChangeChar_apply_of_coprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:45.693309+00:00
-- url     : https://prove2.me/theorems/ad6d731e-0b32-4acc-b1ad-f86d0924439f
-- title:
--   Short Draft Hecke Bridge: base Change Char apply of coprime
-- statement:
--   The Short Draft Hecke Bridge construction uses the base Change Char apply of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/NormFiberCharacters.lean#L146-L160
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/NormFiberCharacters.lean#L146-L160

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
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
open OAI.ShortDraftHeckeBridge

theorem OAI.ShortDraftHeckeBridge.baseChangeChar_apply_of_coprime {q : ℕ}
    (χ : DirichletCharacter ℂ q) (n : ℕ)
    (h : n.Coprime (q * 3)) :
    baseChangeChar χ n = χ n * chiMinusThree n := by sorry
