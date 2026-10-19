-- Prove2me | Theorems.Thm_GapCVP_ThreeCNFReduction_threeCNFSatisfiable_iff
-- name    : GapCVP.ThreeCNFReduction.threeCNFSatisfiable_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:15.527216+00:00
-- url     : https://prove2.me/theorems/b392b50c-c6c0-407c-bc4e-d8f3e63256aa
-- title:
--   GapCVP.ThreeCNFReduction.threeCNFSatisfiable_iff
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

theorem GapCVP.ThreeCNFReduction.threeCNFSatisfiable_iff (formula : ThreeCNF) :
    threeCNFSatisfiable formula ↔
      allDistinct formula ∧
        ∃ assignment : ℕ → Bool, satisfies assignment formula := by sorry
