-- Prove2me | Theorems.Thm_GlobalTheory_JHMult_jhMult_ne_top
-- name    : GlobalTheory.JHMult.jhMult_ne_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:34.562792+00:00
-- url     : https://prove2.me/theorems/c91e9d3c-2efc-4964-8bd0-d1663023186a
-- title:
--   JHMult: jh Mult ne top
-- statement:
--   The JHMult construction uses the jh Mult ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean#L250-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean#L250-L267

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

theorem GlobalTheory.JHMult.jhMult_ne_top {σ : Representation F G W} {ρ : Representation F G V}
    (hσ : σ.IsIrreducible) (h : HasFiniteLength ρ) : jhMult σ ρ ≠ ⊤ := by sorry
