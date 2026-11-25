-- Prove2me | Theorems.Thm_GlobalTheory_Chamber_IsPar_mono
-- name    : GlobalTheory.Chamber.IsPar.mono
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:58:22.231693+00:00
-- url     : https://prove2.me/theorems/c4fd8b57-3d09-4c1e-8587-bebffa160029
-- title:
--   Is Par: mono
-- statement:
--   The Is Par construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/InverseChamberMap.lean#L101-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/InverseChamberMap.lean#L101-L102

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

theorem GlobalTheory.Chamber.IsPar.mono {P Q : Finset (SV k)} (h : IsPar P) (e : Q ⊆ P) : IsPar Q := by sorry
