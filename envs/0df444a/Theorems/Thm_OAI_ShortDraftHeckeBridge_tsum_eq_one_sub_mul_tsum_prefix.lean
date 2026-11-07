-- Prove2me | Theorems.Thm_OAI_ShortDraftHeckeBridge_tsum_eq_one_sub_mul_tsum_prefix
-- name    : OAI.ShortDraftHeckeBridge.tsum_eq_one_sub_mul_tsum_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:13:17.491522+00:00
-- url     : https://prove2.me/theorems/3caa679e-8aae-4e4c-9595-bedce0237e60
-- title:
--   Short Draft Hecke Bridge: tsum eq one sub mul tsum prefix
-- statement:
--   The Short Draft Hecke Bridge construction uses the tsum eq one sub mul tsum prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/LocalEulerIdentities.lean#L597-L632
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/LocalEulerIdentities.lean#L597-L632

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
open Filter Asymptotics
open OAI.ShortDraftHeckeBridge

theorem OAI.ShortDraftHeckeBridge.tsum_eq_one_sub_mul_tsum_prefix
    (a : ℕ → ℂ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : Summable (fun n : ℕ => a n * (r : ℂ) ^ n)) :
    (∑' n : ℕ, a n * (r : ℂ) ^ n) =
      (1 - (r : ℂ)) * (∑' n : ℕ, prefixCoeff a n * (r : ℂ) ^ n) := by sorry
