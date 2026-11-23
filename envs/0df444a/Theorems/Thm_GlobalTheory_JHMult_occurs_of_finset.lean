-- Prove2me | Theorems.Thm_GlobalTheory_JHMult_occurs_of_finset
-- name    : GlobalTheory.JHMult.occurs_of_finset
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:33.8964+00:00
-- url     : https://prove2.me/theorems/f696a384-e36c-4ab9-8bee-4223bb774103
-- title:
--   JHMult: occurs of finset
-- statement:
--   The JHMult construction uses the occurs of finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/JhMultSubAddQuot.lean#L77-L83

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

theorem GlobalTheory.JHMult.occurs_of_finset {σ : Representation F G W} {ρ : Representation F G V} {r : ℕ}
    (A : Finset (Fin r)) (S T : Fin r → Subrepresentation ρ) (h1 : ∀ i, T i ≤ S i)
    (h2 : ∀ i j, i < j → S i ≤ T j) (h3 : ∀ i ∈ A, Step σ (S i) (T i)) :
    OccursTimes σ ρ A.card := by sorry
