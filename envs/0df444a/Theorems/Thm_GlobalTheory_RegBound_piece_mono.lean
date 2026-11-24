-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_piece_mono
-- name    : GlobalTheory.RegBound.piece_mono
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:20:22.986297+00:00
-- url     : https://prove2.me/theorems/2a6e2200-d93c-497e-8a38-f70180323c7a
-- title:
--   Reg Bound: piece mono
-- statement:
--   The Reg Bound construction uses the piece mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L298-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L298-L299

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

theorem GlobalTheory.RegBound.piece_mono {I J : Ideal (MvPolynomial σ K)} (h : I ≤ J) (e : ℕ) :
    piece I e ≤ piece J e := by sorry
