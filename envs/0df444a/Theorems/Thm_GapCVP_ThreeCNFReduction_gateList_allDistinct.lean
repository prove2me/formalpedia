-- Prove2me | Theorems.Thm_GapCVP_ThreeCNFReduction_gateList_allDistinct
-- name    : GapCVP.ThreeCNFReduction.gateList_allDistinct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:15.527216+00:00
-- url     : https://prove2.me/theorems/ebc276cb-8cb1-414b-9aa0-2f228fe20ae5
-- title:
--   GapCVP.ThreeCNFReduction.gateList_allDistinct
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

theorem GapCVP.ThreeCNFReduction.gateList_allDistinct {T S : ℕ}
    (clauseIndex prefixIndex : ℕ)
    (literals : List (SignedLiteral T S)) :
    allDistinct (gateList clauseIndex prefixIndex literals) := by sorry
