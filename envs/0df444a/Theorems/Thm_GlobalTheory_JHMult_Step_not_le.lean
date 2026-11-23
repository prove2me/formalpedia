-- Prove2me | Theorems.Thm_GlobalTheory_JHMult_Step_not_le
-- name    : GlobalTheory.JHMult.Step.not_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:32.953953+00:00
-- url     : https://prove2.me/theorems/a166d8bb-3b02-4c00-840c-f8689be671d0
-- title:
--   Step: not le
-- statement:
--   The Step construction uses the not le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean#L242-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean#L242-L248

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.JHMult
variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]

theorem GlobalTheory.JHMult.Step.not_le {σ : Representation F G W} {ρ : Representation F G V}
    (hσ : σ.IsIrreducible) {S T : Subrepresentation ρ} (h : Step σ S T) : ¬ S ≤ T := by sorry
