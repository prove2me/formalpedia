-- Prove2me | Theorems.Thm_GlobalTheory_BI_invariant_eq_top_of_irreducible
-- name    : GlobalTheory.BI.invariant_eq_top_of_irreducible
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:58:23.246665+00:00
-- url     : https://prove2.me/theorems/aebb3d5d-9238-4eb0-b4cf-d410016a97b0
-- title:
--   BI: invariant eq top of irreducible
-- statement:
--   The BI construction uses the invariant eq top of irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantEqTopOfIrreducible.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantEqTopOfIrreducible.lean#L10-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CommuteImageAbelianByPrimePowerOfNormalCentral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCharacterEigenvectorOfCommutingRepresentat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantEqTopOfIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.BI

theorem GlobalTheory.BI.invariant_eq_top_of_irreducible {k : Type} [Field k] {G : Type} [Group G] {V : Type}
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (h : ρ.IsIrreducible)
    (U : Submodule k V) (hU : ∀ g, ∀ v ∈ U, ρ g v ∈ U) (v : V) (hv : v ∈ U) (hv0 : v ≠ 0) :
    U = ⊤ := by sorry
