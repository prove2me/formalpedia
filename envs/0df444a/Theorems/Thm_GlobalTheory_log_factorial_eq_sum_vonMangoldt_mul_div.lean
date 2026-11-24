-- Prove2me | Theorems.Thm_GlobalTheory_log_factorial_eq_sum_vonMangoldt_mul_div
-- name    : GlobalTheory.log_factorial_eq_sum_vonMangoldt_mul_div
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:08:23.238597+00:00
-- url     : https://prove2.me/theorems/49e36ca7-c31b-40b7-9c29-1186276e97d1
-- title:
--   Global Theory: log factorial eq sum von Mangoldt mul div
-- statement:
--   The Global Theory construction uses the log factorial eq sum von Mangoldt mul div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LogFactorialEqSumVonMangoldtMulDiv.lean#L6-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LogFactorialEqSumVonMangoldtMulDiv.lean#L6-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LogFactorialEqSumVonMangoldtMulDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open GlobalTheory

theorem GlobalTheory.log_factorial_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    Real.log (N.factorial : ℝ) = ∑ n ∈ Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) := by sorry
