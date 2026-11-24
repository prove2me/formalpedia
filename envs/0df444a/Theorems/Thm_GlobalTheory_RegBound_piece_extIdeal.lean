-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_piece_extIdeal
-- name    : GlobalTheory.RegBound.piece_extIdeal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:20:00.469299+00:00
-- url     : https://prove2.me/theorems/30cefa8d-a3ab-4bfa-b5d7-189405edf0cb
-- title:
--   Reg Bound: piece ext Ideal
-- statement:
--   The Reg Bound construction uses the piece ext Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L527-L534
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L527-L534

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
variable {L : Type} [Field L] [Algebra K L]

theorem GlobalTheory.RegBound.piece_extIdeal (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    piece (extIdeal L I) e = extSub L (piece I e) := by sorry
