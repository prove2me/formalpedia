-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_orthoSmall_of_anisoSmall
-- name    : GlobalTheory.SmoothForms.orthoSmall_of_anisoSmall
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:09.744529+00:00
-- url     : https://prove2.me/theorems/7739e418-600c-4d15-a33a-d4fb87ead204
-- title:
--   Smooth Forms: ortho Small of aniso Small
-- statement:
--   The Smooth Forms construction uses the ortho Small of aniso Small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/OrthogonalFrameOfAnisotropicFiniteLengths.lean#L31-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/OrthogonalFrameOfAnisotropicFiniteLengths.lean#L31-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_OrthogonalFrameOfAnisotropicFiniteLengths
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
open Module Submodule

theorem GlobalTheory.SmoothForms.orthoSmall_of_anisoSmall (E : Type) [Field E] [NumberField E] [IsCMField E] (HA : AnisoSmall E) :
    OrthoSmall E := by sorry
