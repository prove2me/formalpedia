-- Prove2me | Theorems.Thm_GapCVP_Comparator_finitePNormGapCVPIsNPHard
-- name    : GapCVP.Comparator.finitePNormGapCVPIsNPHard
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:16.962274+00:00
-- url     : https://prove2.me/theorems/fe19e541-e15b-45b8-8f83-14ff461ba570
-- title:
--   GapCVP.Comparator.finitePNormGapCVPIsNPHard
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
noncomputable section
open scoped BigOperators
open GapCVP.Comparator

theorem GapCVP.Comparator.finitePNormGapCVPIsNPHard (p : ℚ) (hp : 1 ≤ p) :
    IsNPHardPromise (finitePGapCVPPromise p hp) := by sorry
