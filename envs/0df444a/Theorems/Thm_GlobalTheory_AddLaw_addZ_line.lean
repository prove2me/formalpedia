-- Prove2me | Theorems.Thm_GlobalTheory_AddLaw_addZ_line
-- name    : GlobalTheory.AddLaw.addZ_line
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:09:47.053247+00:00
-- url     : https://prove2.me/theorems/f515e56a-c790-42bc-a964-94b62d88ec36
-- title:
--   Add Law: add Z line
-- statement:
--   The Add Law construction uses the add Z line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SubMulOriginD.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SubMulOriginD.lean#L33-L38

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

theorem GlobalTheory.AddLaw.addZ_line (z₁ w₁ z₂ l : R) :
    W.addZ ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] =
      l * W.addX ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)]
      - (w₁ - l * z₁) * W.negAddY ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] := by sorry
