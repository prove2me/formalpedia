-- Prove2me | Theorems.Thm_OAI_NormFiberMult_weighted_norm_fiber_mul
-- name    : OAI.NormFiberMult.weighted_norm_fiber_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:12:56.31488+00:00
-- url     : https://prove2.me/theorems/c036cd4f-3bd4-4011-b31a-534d3cb89632
-- title:
--   Norm Fiber Mult: weighted norm fiber mul
-- statement:
--   The Norm Fiber Mult construction uses the weighted norm fiber mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/LocalEulerIdentities.lean#L296-L351
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/LocalEulerIdentities.lean#L296-L351

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
open OAI.NormFiberMult

theorem OAI.NormFiberMult.weighted_norm_fiber_mul (weight : Ideal O → ℂ)
    (hweight : ∀ I J : Ideal O,
      (Ideal.absNorm I).Coprime (Ideal.absNorm J) →
      weight (I * J) = weight I * weight J)
    (m n : ℕ) (hcop : m.Coprime n) :
    (∑ K ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) (m * n)).toFinset,
       weight K) =
    (∑ I ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) m).toFinset,
       weight I) *
    (∑ J ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset,
       weight J) := by sorry
