-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_Placing_jacquet_equiv
-- name    : GlobalTheory.SmGL.Placing.jacquet_equiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:32.26585+00:00
-- url     : https://prove2.me/theorems/79761c0f-2622-48bb-bd85-66b422ff9e1b
-- title:
--   Placing: jacquet equiv
-- statement:
--   The Placing construction uses the jacquet equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ParIndJacPlacing.lean#L73-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ParIndJacPlacing.lean#L73-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ParIndJacPlacing
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
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Placing
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V]
open ValuativeRel MeasureTheory
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V]

theorem GlobalTheory.SmGL.Placing.jacquet_equiv (π : Representation F G V) {N N' : Subgroup G}
    {s s' : M →* G}
    (hs : ∀ g, s g ∈ Subgroup.normalizer (N : Set G))
    (hs' : ∀ g, s' g ∈ Subgroup.normalizer (N' : Set G)) (χ : M →* Fˣ) (w : G)
    (h : ∀ u ∈ N, w * u * w⁻¹ ∈ N') (h' : ∀ u ∈ N', w⁻¹ * u * w⁻¹⁻¹ ∈ N)
    (hw : ∀ g, w * s g * w⁻¹ = s' g) :
    Nonempty ((_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s hs) χ).Equiv
      (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N' s' hs') χ)) := by sorry
