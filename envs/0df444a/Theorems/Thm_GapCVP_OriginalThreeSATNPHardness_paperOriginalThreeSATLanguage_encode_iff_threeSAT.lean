-- Prove2me | Theorems.Thm_GapCVP_OriginalThreeSATNPHardness_paperOriginalThreeSATLanguage_encode_iff_threeSAT
-- name    : GapCVP.OriginalThreeSATNPHardness.paperOriginalThreeSATLanguage_encode_iff_threeSAT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:16.962274+00:00
-- url     : https://prove2.me/theorems/d949287e-5b36-4aa5-8b38-416b12dcd04a
-- title:
--   GapCVP.OriginalThreeSATNPHardness.paperOriginalThreeSATLanguage_encode_iff_threeSAT
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
open GapCVP.OriginalThreeSATNPHardness
open Computability GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction
open GapCVP.CLStructuralWholeCNFOutputTM GapCVP.CNFFiveFamilySourceIndexedORGadgetFinalCert

theorem GapCVP.OriginalThreeSATNPHardness.paperOriginalThreeSATLanguage_encode_iff_threeSAT
    (formula : ThreeCNF)
    (distinct : allDistinct formula) :
    paperOriginalThreeSATLanguage (encodeThreeCNF formula) ↔
      threeSATLanguage (encodeThreeCNF formula) := by sorry
