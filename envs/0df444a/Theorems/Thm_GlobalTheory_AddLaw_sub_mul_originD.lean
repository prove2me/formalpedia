-- Prove2me | Theorems.Thm_GlobalTheory_AddLaw_sub_mul_originD
-- name    : GlobalTheory.AddLaw.sub_mul_originD
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:09:49.781924+00:00
-- url     : https://prove2.me/theorems/c738c450-1fcc-4514-b11c-b17e717817f0
-- title:
--   Add Law: sub mul origin D
-- statement:
--   The Add Law construction uses the sub mul origin D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SubMulOriginD.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SubMulOriginD.lean#L26-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Projective
open GlobalTheory GlobalTheory.AddLaw
variable {R : Type*} [CommRing R]
variable {W : Projective R}

theorem GlobalTheory.AddLaw.sub_mul_originD {z₁ w₁ z₂ w₂ : R} (h₁ : W.Equation ![z₁, -1, w₁])
    (h₂ : W.Equation ![z₂, -1, w₂]) :
    (w₂ - w₁) * originD W w₁ z₂ w₂ = (z₂ - z₁) * originN W z₁ w₁ z₂ := by sorry
