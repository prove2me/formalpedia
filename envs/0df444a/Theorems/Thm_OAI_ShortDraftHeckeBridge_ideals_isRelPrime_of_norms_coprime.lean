-- Prove2me | Theorems.Thm_OAI_ShortDraftHeckeBridge_ideals_isRelPrime_of_norms_coprime
-- name    : OAI.ShortDraftHeckeBridge.ideals_isRelPrime_of_norms_coprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:07.421461+00:00
-- url     : https://prove2.me/theorems/bb9aada0-e7c4-4c90-b443-2b5162b5c8c0
-- title:
--   Short Draft Hecke Bridge: ideals is Rel Prime of norms coprime
-- statement:
--   The Short Draft Hecke Bridge construction uses the ideals is Rel Prime of norms coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/NormFiberCharacters.lean#L122-L135
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/NormFiberCharacters.lean#L122-L135

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

theorem OAI.ShortDraftHeckeBridge.ideals_isRelPrime_of_norms_coprime (I J : Ideal O)
    (h : (Ideal.absNorm I).Coprime (Ideal.absNorm J)) :
    IsRelPrime I J := by sorry
