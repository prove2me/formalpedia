-- Prove2me | Theorems.Thm_GlobalTheory_ContraRefl_mem_of_annihilator_eq_bot
-- name    : GlobalTheory.ContraRefl.mem_of_annihilator_eq_bot
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:25:50.173864+00:00
-- url     : https://prove2.me/theorems/c2ad7a64-0358-454f-9a71-0e8a4ca8e0f8
-- title:
--   Contra Refl: mem of annihilator eq bot
-- statement:
--   The Contra Refl construction uses the mem of annihilator eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SmoothContragredientIrreducibleAndReflexive.lean#L246-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SmoothContragredientIrreducibleAndReflexive.lean#L246-L287

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

theorem GlobalTheory.ContraRefl.mem_of_annihilator_eq_bot
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {π : Representation ℂ G V} (hπ : IsAdmissible π) (U : Subrepresentation (contra π))
    (hA : ∀ v : V, (∀ u ∈ U.toSubmodule, (u : Module.Dual ℂ V) v = 0) → v = 0)
    (l : smoothPart π.dual) : l ∈ U.toSubmodule := by sorry
