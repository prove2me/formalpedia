-- Prove2me | Theorems.Thm_GlobalTheory_Chamber_IsOrth_sub_mem_span
-- name    : GlobalTheory.Chamber.IsOrth.sub_mem_span
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:58:30.854804+00:00
-- url     : https://prove2.me/theorems/5954b523-ddad-4a1e-8a52-8a47bda5427f
-- title:
--   Is Orth: sub mem span
-- statement:
--   The Is Orth construction uses the sub mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/InverseChamberMap.lean#L194-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/InverseChamberMap.lean#L194-L208

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

theorem GlobalTheory.Chamber.IsOrth.sub_mem_span {𝔞 : Submodule ℝ (A0 k)} {X : Finset (SV k) → A0 k} (h : IsOrth 𝔞 X) {P P' : Finset (SV k)}
    (hP : P ∈ parP 𝔞 ∅) (hP' : P' ∈ parP 𝔞 ∅) {u : SV k} (hu : u ∈ P) (e : P.erase u ⊆ P') :
    X P - X P' ∈ Submodule.span ℝ {rt P u} := by sorry
