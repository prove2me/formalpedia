-- Prove2me | Theorems.Thm_GapCVP_CLStructuralWholeCNFOutputTM_structuralWholeCNFWord_mem_threeSAT_iff
-- name    : GapCVP.CLStructuralWholeCNFOutputTM.structuralWholeCNFWord_mem_threeSAT_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:16.962274+00:00
-- url     : https://prove2.me/theorems/fd822fb0-5025-4bd7-bd0e-dd99d56d1a65
-- title:
--   GapCVP.CLStructuralWholeCNFOutputTM.structuralWholeCNFWord_mem_threeSAT_iff
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
open GapCVP.CLStructuralWholeCNFOutputTM
open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLCellRowBounds GapCVP.CLCompleteVerifierSimulation
open GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction

theorem GapCVP.CLStructuralWholeCNFOutputTM.structuralWholeCNFWord_mem_threeSAT_iff
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :
    threeSATLanguage (structuralWholeCNFWord bound machine x) ↔
      ∃ certificate : List Bool,
        certificate.length ≤ bound.eval x.length ∧
          verifier (x, certificate) = true := by sorry
