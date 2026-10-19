-- Prove2me | Theorems.Thm_GapCVP_CLNondeterminism_compiledTableau_iff_verifier
-- name    : GapCVP.CLNondeterminism.compiledTableau_iff_verifier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:16.962274+00:00
-- url     : https://prove2.me/theorems/10f3b12e-6b61-4234-995a-6ad39a8444bc
-- title:
--   GapCVP.CLNondeterminism.compiledTableau_iff_verifier
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
open GapCVP.CLNondeterminism
open Computability GapCVP.CLVerifier

theorem GapCVP.CLNondeterminism.compiledTableau_iff_verifier
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (compiler : LocalTableauCompiler bound machine)
    (x : List Bool) :
    threeSATLanguage
      (encodedTableau
        (tableauSimulationOfLocalCompiler bound machine compiler) x) ↔
      ∃ certificate : List Bool,
        certificate.length ≤ bound.eval x.length ∧
          verifier (x, certificate) = true := by sorry
