-- Prove2me | Theorems.Thm_GlobalTheory_BI_finrank_eq_one_or_imprimitive
-- name    : GlobalTheory.BI.finrank_eq_one_or_imprimitive
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:58:23.157223+00:00
-- url     : https://prove2.me/theorems/ba75b3de-0e50-40bc-b88f-0b1ff65876ce
-- title:
--   BI: finrank eq one or imprimitive
-- statement:
--   The BI construction uses the finrank eq one or imprimitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantEqTopOfIrreducible.lean#L19-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantEqTopOfIrreducible.lean#L19-L111

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

theorem GlobalTheory.BI.finrank_eq_one_or_imprimitive : ∀ (k : Type) [Field k] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k], AbByP G → ρ.IsIrreducible → Module.finrank k V = 1 ∨ ∃ (T : Subgroup G) (W : Submodule k V), T ≠ ⊤ ∧ (∀ t ∈ T, ∀ w ∈ W, ρ t w ∈ W) ∧ iSupIndep (fun q : G ⧸ T => W.map (ρ q.out)) ∧ ⨆ q : G ⧸ T, W.map (ρ q.out) = ⊤ := by sorry
