-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_mem_map_rep
-- name    : GlobalTheory.FinWeil.mem_map_rep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:14.252007+00:00
-- url     : https://prove2.me/theorems/5d6c4a28-7c29-48da-8529-b87ad383dc42
-- title:
--   Fin Weil: mem map rep
-- statement:
--   The Fin Weil construction uses the mem map rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsWeilRepresentationHeisenberg.lean#L24-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsWeilRepresentationHeisenberg.lean#L24-L33

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

theorem GlobalTheory.FinWeil.mem_map_rep {Γ : Type} [Group Γ] (ρ : Γ →* Module.End R X) (g : Γ)
    (A : Submodule R X) (x : X) :
    x ∈ A.map (ρ g) ↔ ρ g⁻¹ x ∈ A := by sorry
