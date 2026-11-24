-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_frameSmall
-- name    : GlobalTheory.SmoothForms.frameSmall
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:17.168791+00:00
-- url     : https://prove2.me/theorems/efdd68b4-88fc-497f-ae23-409a1579ca3a
-- title:
--   Smooth Forms: frame Small
-- statement:
--   The Smooth Forms construction uses the frame Small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/OrthogonalAnisotropicFrameBoundedCM.lean#L157-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/OrthogonalAnisotropicFrameBoundedCM.lean#L157-L163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_OrthogonalAnisotropicFrameBoundedCM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.SmoothForms.frameSmall : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], FrameSmall E := by sorry
