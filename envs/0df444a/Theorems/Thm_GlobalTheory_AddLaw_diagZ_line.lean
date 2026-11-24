-- Prove2me | Theorems.Thm_GlobalTheory_AddLaw_diagZ_line
-- name    : GlobalTheory.AddLaw.diagZ_line
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:10:54.49016+00:00
-- url     : https://prove2.me/theorems/051686f5-54fd-4f6b-af27-d16e1e40abf3
-- title:
--   Add Law: diag Z line
-- statement:
--   The Add Law construction uses the diag Z line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SubMulOriginD.lean#L55-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SubMulOriginD.lean#L55-L93

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

theorem GlobalTheory.AddLaw.diagZ_line {z₁ w₁ z₂ l : R} (h₁ : W.Equation ![z₁, -1, w₁])
    (hl : originN W z₁ w₁ z₂ = l * originD W w₁ z₂ (w₁ + l * (z₂ - z₁))) :
    diagZ W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] =
      l * diagX W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)]
      - (w₁ - l * z₁) * negDiagY W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] := by sorry
