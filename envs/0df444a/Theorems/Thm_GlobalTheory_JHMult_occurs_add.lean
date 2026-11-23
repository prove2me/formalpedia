-- Prove2me | Theorems.Thm_GlobalTheory_JHMult_occurs_add
-- name    : GlobalTheory.JHMult.occurs_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:17.920332+00:00
-- url     : https://prove2.me/theorems/42640e41-db0e-41b9-8174-96f50e0063da
-- title:
--   JHMult: occurs add
-- statement:
--   The JHMult construction uses the occurs add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean#L162-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean#L162-L201

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

theorem GlobalTheory.JHMult.occurs_add (hι : Function.Injective ι) (hp : Function.Surjective p)
    (h0 : ∀ u, p (ι u) = 0) {a b : ℕ} (ha : OccursTimes σ ρ₁ a) (hb : OccursTimes σ ρ₂ b) :
    OccursTimes σ ρ (a + b) := by sorry
