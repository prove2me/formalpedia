-- Prove2me | Theorems.Thm_GapCVP_OriginalThreeSATNPHardness_structuralWholeCNFWord_mem_paperOriginalThreeSAT_iff
-- name    : GapCVP.OriginalThreeSATNPHardness.structuralWholeCNFWord_mem_paperOriginalThreeSAT_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:16.962274+00:00
-- url     : https://prove2.me/theorems/8fd2f656-de75-41f4-9817-cc3484525cd4
-- title:
--   GapCVP.OriginalThreeSATNPHardness.structuralWholeCNFWord_mem_paperOriginalThreeSAT_iff
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

theorem GapCVP.OriginalThreeSATNPHardness.structuralWholeCNFWord_mem_paperOriginalThreeSAT_iff
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) :
    paperOriginalThreeSATLanguage
        (structuralWholeCNFWord bound machine input) ↔
      ∃ certificate : List Bool,
        certificate.length ≤ bound.eval input.length ∧
          verifier (input, certificate) = true := by sorry
