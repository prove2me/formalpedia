-- Prove2me | Theorems.Thm_GlobalTheory_JHMult_step_dichotomy
-- name    : GlobalTheory.JHMult.step_dichotomy
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:56.922704+00:00
-- url     : https://prove2.me/theorems/a1ac6951-f9a8-4665-8fe9-0d7fd5ece515
-- title:
--   JHMult: step dichotomy
-- statement:
--   The JHMult construction uses the step dichotomy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean#L93-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean#L93-L130

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
variable {σ : Representation F G W} {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
  {ρ₂ : Representation F G V₂} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)

theorem GlobalTheory.JHMult.step_dichotomy (hσ : σ.IsIrreducible) (hker : ∀ v, p v = 0 → ∃ u, ι u = v)
    {S T : Subrepresentation ρ} (hTS : T ≤ S) (h : Step σ S T) :
    Step σ (subComap ι S) (subComap ι T) ∨ Step σ (subMap p S) (subMap p T) := by sorry
