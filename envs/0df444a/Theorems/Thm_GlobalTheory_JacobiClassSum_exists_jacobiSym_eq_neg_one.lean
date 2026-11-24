-- Prove2me | Theorems.Thm_GlobalTheory_JacobiClassSum_exists_jacobiSym_eq_neg_one
-- name    : GlobalTheory.JacobiClassSum.exists_jacobiSym_eq_neg_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:50:43.457736+00:00
-- url     : https://prove2.me/theorems/1a0f4372-fb62-406e-bf9b-45cef09c8773
-- title:
--   Jacobi Class Sum: exists jacobi Sym eq neg one
-- statement:
--   The Jacobi Class Sum construction uses the exists jacobi Sym eq neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsJacobiSymEqNegOne.lean#L8-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsJacobiSymEqNegOne.lean#L8-L32

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

theorem GlobalTheory.JacobiClassSum.exists_jacobiSym_eq_neg_one {s : ℕ} (h1 : 1 < s) (hodd : Odd s) (hsq : Squarefree s) :
    ∃ c : ℕ, jacobiSym (c : ℤ) s = -1 := by sorry
