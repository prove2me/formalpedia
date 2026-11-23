-- Prove2me | Theorems.Thm_GlobalTheory_ContraRefl_contra_isIrreducible
-- name    : GlobalTheory.ContraRefl.contra_isIrreducible
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:14.401891+00:00
-- url     : https://prove2.me/theorems/0272a3fb-ddb6-4ef9-97b7-d036d437c8bb
-- title:
--   Contra Refl: contra is Irreducible
-- statement:
--   The Contra Refl construction uses the contra is Irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SmoothContragredientIrreducibleAndReflexive.lean#L289-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SmoothContragredientIrreducibleAndReflexive.lean#L289-L327

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.ContraRefl
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.ContraRefl.contra_isIrreducible
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {π : Representation ℂ G V} (hπ : IsAdmissible π) (hirr : π.IsIrreducible) :
    (contra π).IsIrreducible := by sorry
