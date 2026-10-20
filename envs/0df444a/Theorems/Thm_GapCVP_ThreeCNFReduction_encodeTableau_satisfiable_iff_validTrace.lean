-- Prove2me | Theorems.Thm_GapCVP_ThreeCNFReduction_encodeTableau_satisfiable_iff_validTrace
-- name    : GapCVP.ThreeCNFReduction.encodeTableau_satisfiable_iff_validTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:16.962274+00:00
-- url     : https://prove2.me/theorems/bd38cb56-9f59-416d-a221-0f8dd57f37c8
-- title:
--   GapCVP.ThreeCNFReduction.encodeTableau_satisfiable_iff_validTrace
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

theorem GapCVP.ThreeCNFReduction.encodeTableau_satisfiable_iff_validTrace {T S : ℕ}
    (spec : Specification T S) :
    threeCNFSatisfiable (encodeTableau spec) ↔
      ∃ trace : Time T → Position T → Symbol S,
        ValidTrace spec trace := by sorry
