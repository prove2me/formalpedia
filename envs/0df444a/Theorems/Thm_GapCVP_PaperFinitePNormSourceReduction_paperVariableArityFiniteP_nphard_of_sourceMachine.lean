-- Prove2me | Theorems.Thm_GapCVP_PaperFinitePNormSourceReduction_paperVariableArityFiniteP_nphard_of_sourceMachine
-- name    : GapCVP.PaperFinitePNormSourceReduction.paperVariableArityFiniteP_nphard_of_sourceMachine
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:16.962274+00:00
-- url     : https://prove2.me/theorems/e6bf3094-8978-4593-bfc8-0f1b000f79bf
-- title:
--   GapCVP.PaperFinitePNormSourceReduction.paperVariableArityFiniteP_nphard_of_sourceMachine
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
open GapCVP.PaperFinitePNormSourceReduction
open scoped BigOperators
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.Factor400BinaryCodeDecodingCorollary
open GapCVP.Factor400BinaryInstanceBridge GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.OriginalThreeSATNPHardness
open GapCVP.SourcePreprocessingSemantics GapCVP.SourcePreprocessingTM GapCVP.FormulaBridge
open GapCVP.FourFamilySoundness GapCVP.NormalizedRecordDecoder GapCVP.PhysicalWordSoundness
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.Factor400FinitePNormCorollary GapCVP.Factor400FinitePNormPromiseReduction
open GapCVP.Factor400FinitePNormSourceReduction GapCVP.Factor400FinitePNormUnconditional
open GapCVP.Factor400FinitePRadiusArithmetic GapCVP.Factor400FinitePRadiusBounds

theorem GapCVP.PaperFinitePNormSourceReduction.paperVariableArityFiniteP_nphard_of_sourceMachine
    (p : ℚ) (hp : 1 ≤ p)
    (machine : BitTM (paperVariableArityFinitePSourceMap p hp)) :
    NPHardPromise (finitePGapCVPPromise p hp) := by sorry
