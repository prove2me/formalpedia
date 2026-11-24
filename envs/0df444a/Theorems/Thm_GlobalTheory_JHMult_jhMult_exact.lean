-- Prove2me | Theorems.Thm_GlobalTheory_JHMult_jhMult_exact
-- name    : GlobalTheory.JHMult.jhMult_exact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:37.947803+00:00
-- url     : https://prove2.me/theorems/6b9cf50a-72e0-466c-a171-be9b060b8ac4
-- title:
--   JHMult: jh Mult exact
-- statement:
--   The JHMult construction uses the jh Mult exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean#L203-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean#L203-L225

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

theorem GlobalTheory.JHMult.jhMult_exact (hσ : σ.IsIrreducible) (hι : Function.Injective ι)
    (hp : Function.Surjective p) (h0 : ∀ u, p (ι u) = 0) (hker : ∀ v, p v = 0 → ∃ u, ι u = v) :
    jhMult σ ρ = jhMult σ ρ₁ + jhMult σ ρ₂ := by sorry
