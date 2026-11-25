-- Prove2me | Theorems.Thm_GlobalTheory_sum_cn_isSquare_le
-- name    : GlobalTheory.sum_cn_isSquare_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:22:54.080158+00:00
-- url     : https://prove2.me/theorems/5991c8dc-0fb8-4aa0-acf8-f71c6e71b6b5
-- title:
--   Global Theory: sum cn is Square le
-- statement:
--   The Global Theory construction uses the sum cn is Square le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumVonMangoldtDivSqIocLe.lean#L53-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumVonMangoldtDivSqIocLe.lean#L53-L110

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqIocLe
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

theorem GlobalTheory.sum_cn_isSquare_le
    (h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (x : ℝ) (hx : 1 ≤ x) (N : ℕ) :
    ∑ n ∈ (Icc 1 N).filter (fun n => IsSquare n), Formalism.HermitianLattices.GL2PrimeSums.cn x n ≤ 10 * Real.sqrt x := by sorry
