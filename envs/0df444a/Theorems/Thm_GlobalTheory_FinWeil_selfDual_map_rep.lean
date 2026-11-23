-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_selfDual_map_rep
-- name    : GlobalTheory.FinWeil.selfDual_map_rep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:32.809652+00:00
-- url     : https://prove2.me/theorems/029a8b8e-5e30-46ba-bdee-2e7528392677
-- title:
--   Fin Weil: self Dual map rep
-- statement:
--   The Fin Weil construction uses the self Dual map rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsWeilRepresentationHeisenberg.lean#L38-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsWeilRepresentationHeisenberg.lean#L38-L51

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

theorem GlobalTheory.FinWeil.selfDual_map_rep {γ : X → X → ℂ} {Γ : Type} [Group Γ]
    (ρ : Γ →* Module.End R X)
    (hρ : ∀ g x y, γ (ρ g x) (ρ g y) = γ x y) {A : Submodule R X} (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A)
    (g : Γ) :
    _root_.GlobalTheory.FinWeil.SelfDual γ (A.map (ρ g)) := by sorry
