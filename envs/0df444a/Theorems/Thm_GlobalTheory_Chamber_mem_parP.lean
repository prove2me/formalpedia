-- Prove2me | Theorems.Thm_GlobalTheory_Chamber_mem_parP
-- name    : GlobalTheory.Chamber.mem_parP
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:58.057906+00:00
-- url     : https://prove2.me/theorems/9866d475-e5cd-4c08-a627-aa3fe4b1adca
-- title:
--   Chamber: mem par P
-- statement:
--   The Chamber construction uses the mem par P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/InverseChamberMap.lean#L98-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/InverseChamberMap.lean#L98-L99

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

theorem GlobalTheory.Chamber.mem_parP {𝔞 : Submodule ℝ (A0 k)} {R P : Finset (SV k)} : P ∈ parP 𝔞 R ↔ IsPar P ∧ aP P = 𝔞 ∧ R ⊆ P := by sorry
