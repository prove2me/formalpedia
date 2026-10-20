-- Prove2me | Theorems.Thm_GapCVP_Comparator_binaryNearestCodeword_yes_iff_original
-- name    : GapCVP.Comparator.binaryNearestCodeword_yes_iff_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:16.962274+00:00
-- url     : https://prove2.me/theorems/b8d35bd7-9c4f-42f3-9013-32d404bc19c8
-- title:
--   GapCVP.Comparator.binaryNearestCodeword_yes_iff_original
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

theorem GapCVP.Comparator.binaryNearestCodeword_yes_iff_original (bits : List Bool) :
    binaryNearestCodewordPromise.yes bits ↔
      GapCVP.Factor400BinaryDecodingPromiseHardness.binaryNearestCodewordPromise.yes bits := by sorry
