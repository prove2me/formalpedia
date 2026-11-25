-- Prove2me | Theorems.Thm_GlobalTheory_Chamber_IsOrth_isGMFam
-- name    : GlobalTheory.Chamber.IsOrth.isGMFam
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:58:31.719592+00:00
-- url     : https://prove2.me/theorems/95d9da8d-9503-49af-b62a-ccb829d60d33
-- title:
--   Is Orth: is GMFam
-- statement:
--   The Is Orth construction uses the is GMFam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/InverseChamberMap.lean#L210-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/InverseChamberMap.lean#L210-L213

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

theorem GlobalTheory.Chamber.IsOrth.isGMFam {𝔞 : Submodule ℝ (A0 k)} {X : Finset (SV k) → A0 k} (h : IsOrth 𝔞 X) : IsGMFam 𝔞 (expFam X) := by sorry
