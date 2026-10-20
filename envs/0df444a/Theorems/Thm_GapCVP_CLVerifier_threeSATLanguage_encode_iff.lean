-- Prove2me | Theorems.Thm_GapCVP_CLVerifier_threeSATLanguage_encode_iff
-- name    : GapCVP.CLVerifier.threeSATLanguage_encode_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:16.962274+00:00
-- url     : https://prove2.me/theorems/98f42c2c-52b0-4a8a-9664-4b0083d5918a
-- title:
--   GapCVP.CLVerifier.threeSATLanguage_encode_iff
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
open GapCVP.CLVerifier
open Computability GapCVP.CL

theorem GapCVP.CLVerifier.threeSATLanguage_encode_iff (formula : ThreeCNF) :
    threeSATLanguage ((binaryFinEncoding ThreeCNF).encode formula) ↔
      threeCNFSatisfiable formula := by sorry
