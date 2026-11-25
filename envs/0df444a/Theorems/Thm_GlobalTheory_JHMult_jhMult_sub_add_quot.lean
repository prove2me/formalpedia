-- Prove2me | Theorems.Thm_GlobalTheory_JHMult_jhMult_sub_add_quot
-- name    : GlobalTheory.JHMult.jhMult_sub_add_quot
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:11:36.535268+00:00
-- url     : https://prove2.me/theorems/82b88626-2551-4269-bc50-6e42cddcb431
-- title:
--   JHMult: jh Mult sub add quot
-- statement:
--   The JHMult construction uses the jh Mult sub add quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean#L229-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean#L229-L240

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

theorem GlobalTheory.JHMult.jhMult_sub_add_quot {σ : Representation F G W} {ρ : Representation F G V}
    (hσ : σ.IsIrreducible) (S : Subrepresentation ρ) :
    jhMult σ ρ = jhMult σ S.toRepresentation + jhMult σ (subQuot ⊤ S) := by sorry
