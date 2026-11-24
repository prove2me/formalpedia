-- Prove2me | Theorems.Thm_GlobalTheory_ContraRefl_contra_irreducible_reflexive
-- name    : GlobalTheory.ContraRefl.contra_irreducible_reflexive
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:25:59.051579+00:00
-- url     : https://prove2.me/theorems/4c9e7e89-702e-414b-9a3a-7489d5a02b2c
-- title:
--   Contra Refl: contra irreducible reflexive
-- statement:
--   The Contra Refl construction uses the contra irreducible reflexive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SmoothContragredientIrreducibleAndReflexive.lean#L367-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SmoothContragredientIrreducibleAndReflexive.lean#L367-L370

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

theorem GlobalTheory.ContraRefl.contra_irreducible_reflexive : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (π' : Representation ℂ G W), IsAdmissible π → IsAdmissible π' → (π.IsIrreducible → (contra π).IsIrreducible) ∧ Nonempty (π.Equiv (contra (contra π))) ∧ (Nonempty ((contra π).Equiv (contra π')) → Nonempty (π.Equiv π')) := by sorry
