-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_lipschitzOneVariableKernel_two_eq_indicator
-- name    : GlobalTheory.HeckeTwo.lipschitzOneVariableKernel_two_eq_indicator
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:14:25.203668+00:00
-- url     : https://prove2.me/theorems/90d9436d-b3c9-4dfe-aa8b-21bf9cc4a9b8
-- title:
--   Hecke Two: lipschitz One Variable Kernel two eq indicator
-- statement:
--   The Hecke Two construction uses the lipschitz One Variable Kernel two eq indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformSigmaZeroEq.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformSigmaZeroEq.lean#L13-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierLipschitzOneVariableKernelEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousIsBigORpowLipschitzProductKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformSigmaZeroEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set
open scoped FourierTransform
open GlobalTheory GlobalTheory.HeckeTwo

theorem GlobalTheory.HeckeTwo.lipschitzOneVariableKernel_two_eq_indicator {y : ℝ} (hy : 0 < y) :
    GlobalTheory.LipschitzTR.phi1 2 ((y : ℂ) * I) =
      (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ 1 * Complex.exp (-(((2 * Real.pi * y : ℝ) : ℂ) * t))) := by sorry
