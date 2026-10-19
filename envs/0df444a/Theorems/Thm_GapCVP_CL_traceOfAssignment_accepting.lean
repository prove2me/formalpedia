-- Prove2me | Theorems.Thm_GapCVP_CL_traceOfAssignment_accepting
-- name    : GapCVP.CL.traceOfAssignment_accepting
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:15.527216+00:00
-- url     : https://prove2.me/theorems/26d54649-01fb-48bb-a97f-76d9e9da86e3
-- title:
--   GapCVP.CL.traceOfAssignment_accepting
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
open GapCVP.CL

theorem GapCVP.CL.traceOfAssignment_accepting {T S : ℕ}
    (spec : Specification T S)
    (assignment : Variable T S → Bool)
    (hsat : satisfiesFormula assignment (tableauFormula spec)) :
    ∃ i : Position T,
      traceOfAssignment spec assignment hsat (Fin.last T) i = spec.accept := by sorry
