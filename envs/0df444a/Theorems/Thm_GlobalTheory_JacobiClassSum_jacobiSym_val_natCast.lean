-- Prove2me | Theorems.Thm_GlobalTheory_JacobiClassSum_jacobiSym_val_natCast
-- name    : GlobalTheory.JacobiClassSum.jacobiSym_val_natCast
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:50:51.955935+00:00
-- url     : https://prove2.me/theorems/2977752a-017a-489b-916a-02bda3fa3aeb
-- title:
--   Jacobi Class Sum: jacobi Sym val nat Cast
-- statement:
--   The Jacobi Class Sum construction uses the jacobi Sym val nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsJacobiSymEqNegOne.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsJacobiSymEqNegOne.lean#L34-L36

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

theorem GlobalTheory.JacobiClassSum.jacobiSym_val_natCast {s : ℕ} [NeZero s] (b : ℕ) :
    jacobiSym (((b : ZMod s).val : ℕ) : ℤ) s = jacobiSym (b : ℤ) s := by sorry
