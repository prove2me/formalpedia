-- Prove2me | Theorems.Thm_GapCVP_nphardPromise_of_nphard_of_promiseReduction
-- name    : GapCVP.nphardPromise_of_nphard_of_promiseReduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:15.527216+00:00
-- url     : https://prove2.me/theorems/074d9817-1dda-4e2c-be6a-583dc6cd9734
-- title:
--   GapCVP.nphardPromise_of_nphard_of_promiseReduction
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

theorem GapCVP.nphardPromise_of_nphard_of_promiseReduction
    {A : BitLanguage} {P : PromiseProblem} (hard : NPHard A)
    (reduction : PromiseReduction A P)
    (closed : PolynomialTimeClosedUnderComposition) : NPHardPromise P := by sorry
