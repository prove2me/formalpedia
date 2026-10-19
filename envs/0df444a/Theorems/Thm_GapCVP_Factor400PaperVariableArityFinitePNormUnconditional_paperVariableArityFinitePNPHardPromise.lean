-- Prove2me | Theorems.Thm_GapCVP_Factor400PaperVariableArityFinitePNormUnconditional_paperVariableArityFinitePNPHardPromise
-- name    : GapCVP.Factor400PaperVariableArityFinitePNormUnconditional.paperVariableArityFinitePNPHardPromise
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:16.962274+00:00
-- url     : https://prove2.me/theorems/7a1d2de0-15c8-4e94-965a-a3d5b7cea1cc
-- title:
--   GapCVP.Factor400PaperVariableArityFinitePNormUnconditional.paperVariableArityFinitePNPHardPromise
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
open GapCVP.Factor400PaperVariableArityFinitePNormUnconditional
open Turing GapCVP.BinaryEncoding GapCVP.CNFBoundedRecordFoldTM
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputPolynomialCompositionClosure
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.Factor400BinaryCodeDecodingCorollary
open GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge GapCVP.FourFamilySoundness
open GapCVP.CanonicalMatrixShape GapCVP.CanonicalPhysicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalMatrixCellInstantiation
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalRadiusMachine
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.PhysicalNormalizedBranchTM GapCVP.PhysicalNormalizedCanonicalGuardTM
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianSourceConsistencyBridge
open GapCVP.GaussianExactSourceInitializer GapCVP.GaussianSourceInitializerInstantiation
open GapCVP.GaussianOutputSerializerTM GapCVP.ExactPhysicalSourceTM
open GapCVP.Factor400FinitePNormCorollary GapCVP.Factor400FinitePNormPromiseReduction
open GapCVP.Factor400FinitePRadiusArithmetic GapCVP.Factor400FinitePRadiusSourceTM
open GapCVP.Factor400FinitePRadiusRationalAtomTM GapCVP.PaperFinitePNormSourceReduction

theorem GapCVP.Factor400PaperVariableArityFinitePNormUnconditional.paperVariableArityFinitePNPHardPromise
    (p : ℚ) (hp : 1 ≤ p) :
    NPHardPromise (finitePGapCVPPromise p hp) := by sorry
