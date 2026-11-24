-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_isHeis_comp_rep
-- name    : GlobalTheory.FinWeil.isHeis_comp_rep
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:30:48.933123+00:00
-- url     : https://prove2.me/theorems/8d5a45bb-ca94-4eb5-91d3-d5d03699bb56
-- title:
--   Fin Weil: is Heis comp rep
-- statement:
--   The Fin Weil construction uses the is Heis comp rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsWeilRepresentationHeisenberg.lean#L56-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsWeilRepresentationHeisenberg.lean#L56-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedHeisenbergIntertwinerComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsWeilRepresentationHeisenberg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
open Classical
open scoped BigOperators
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.FinWeil.isHeis_comp_rep {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    {Γ : Type} [Group Γ] (ρ : Γ →* Module.End R X)
    (hρ : ∀ g x y, γ (ρ g x) (ρ g y) = γ x y) (g : Γ) :
    _root_.GlobalTheory.FinWeil.IsHeis σ w γ (fun x => W (ρ g x)) := by sorry
