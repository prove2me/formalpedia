-- Prove2me | Theorems.Thm_GlobalTheory_Chamber_IsGMFam_mul
-- name    : GlobalTheory.Chamber.IsGMFam.mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:58:18.134861+00:00
-- url     : https://prove2.me/theorems/db0e1975-1ce6-411e-acf3-542ae7cae5ed
-- title:
--   Is GMFam: mul
-- statement:
--   The Is GMFam construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/InverseChamberMap.lean#L215-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/InverseChamberMap.lean#L215-L217

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_InverseChamberMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace ContDiff Classical
open GlobalTheory GlobalTheory.Chamber
variable {k : ℕ}

theorem GlobalTheory.Chamber.IsGMFam.mul {𝔞 : Submodule ℝ (A0 k)} {c d : Finset (SV k) → A0 k → ℂ} (h : IsGMFam 𝔞 c) (h' : IsGMFam 𝔞 d) :
    IsGMFam 𝔞 (c * d) := by sorry
