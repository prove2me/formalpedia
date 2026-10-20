-- Prove2me | Theorems.Thm_GapCVP_Comparator_binarySyndromeDecoding_yes_iff_original
-- name    : GapCVP.Comparator.binarySyndromeDecoding_yes_iff_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:16.962274+00:00
-- url     : https://prove2.me/theorems/1b199d16-8421-4706-a24f-75593a8fedb3
-- title:
--   GapCVP.Comparator.binarySyndromeDecoding_yes_iff_original
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

theorem GapCVP.Comparator.binarySyndromeDecoding_yes_iff_original (bits : List Bool) :
    binarySyndromeDecodingPromise.yes bits ↔
      GapCVP.Factor400BinaryDecodingPromiseHardness.binarySyndromeDecodingPromise.yes bits := by sorry
