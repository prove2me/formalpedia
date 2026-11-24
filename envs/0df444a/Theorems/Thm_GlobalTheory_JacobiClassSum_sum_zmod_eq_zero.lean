-- Prove2me | Theorems.Thm_GlobalTheory_JacobiClassSum_sum_zmod_eq_zero
-- name    : GlobalTheory.JacobiClassSum.sum_zmod_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:50:41.519505+00:00
-- url     : https://prove2.me/theorems/71a2e058-9aaf-4c85-baa3-e674153d2855
-- title:
--   Jacobi Class Sum: sum zmod eq zero
-- statement:
--   The Jacobi Class Sum construction uses the sum zmod eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsJacobiSymEqNegOne.lean#L38-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsJacobiSymEqNegOne.lean#L38-L57

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsJacobiSymEqNegOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.JacobiClassSum

theorem GlobalTheory.JacobiClassSum.sum_zmod_eq_zero {s : ℕ} [NeZero s] (h1 : 1 < s) (hodd : Odd s) (hsq : Squarefree s) :
    ∑ x : ZMod s, jacobiSym ((x.val : ℕ) : ℤ) s = 0 := by sorry
