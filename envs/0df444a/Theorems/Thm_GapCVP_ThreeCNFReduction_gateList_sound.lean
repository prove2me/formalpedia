-- Prove2me | Theorems.Thm_GapCVP_ThreeCNFReduction_gateList_sound
-- name    : GapCVP.ThreeCNFReduction.gateList_sound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:15.527216+00:00
-- url     : https://prove2.me/theorems/956ebb81-a964-4614-a082-8c6ae62c477e
-- title:
--   GapCVP.ThreeCNFReduction.gateList_sound
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | GapCVP | external Lean 4.33.1 validation; bundle SHA256 48b1efd821d2a3e34fadc0f98ff0604b418a7647736e5b368a2e5f6364a2fcb0

import Mathlib
import Definitions.Def_GapCVP
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.ThreeCNFReduction
open GapCVP.CL

theorem GapCVP.ThreeCNFReduction.gateList_sound {T S : ℕ}
    (assignment : ℕ → Bool)
    (clauseIndex prefixIndex : ℕ)
    (literals : List (SignedLiteral T S))
    (hgates : satisfies assignment
      (gateList clauseIndex prefixIndex literals))
    (hstart : assignment
      (accumulatorVariable clauseIndex prefixIndex) = true)
    (hfinish : assignment
      (accumulatorVariable clauseIndex
        (prefixIndex + literals.length)) = false) :
    ∃ literal ∈ literals,
      assignment (sourceVariable literal.1) = literal.2 := by sorry
