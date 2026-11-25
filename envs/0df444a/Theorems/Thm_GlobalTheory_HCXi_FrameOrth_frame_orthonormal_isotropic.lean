-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_FrameOrth_frame_orthonormal_isotropic
-- name    : GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:46:43.224936+00:00
-- url     : https://prove2.me/theorems/abd507fb-c5a4-4c16-b25e-006314e49d15
-- title:
--   Frame Orth: frame orthonormal isotropic
-- statement:
--   The Frame Orth construction uses the frame orthonormal isotropic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FrameIsotropicOrthonormal.lean#L39-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FrameIsotropicOrthonormal.lean#L39-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.FrameOrth

theorem GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic : ∀ k r : ℕ, 1 ≤ k →
    (frame k r)ᴴ * frame k r = 1 ∧ (frame k r)ᴴ * Hpk k r * frame k r = 0 := by sorry
