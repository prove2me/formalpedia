-- Prove2me | Theorems.Thm_GlobalTheory_BI_pair_character_eq_finrank
-- name    : GlobalTheory.BI.pair_character_eq_finrank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:26.355726+00:00
-- url     : https://prove2.me/theorems/6b6deaca-2068-4731-933a-512ce123c57e
-- title:
--   BI: pair character eq finrank
-- statement:
--   The BI construction uses the pair character eq finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FiniteGroupFunctionPairingCharacterEqFinrankInte.lean#L6-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FiniteGroupFunctionPairingCharacterEqFinrankInte.lean#L6-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingCharacterEqFinrankInte
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI

theorem GlobalTheory.BI.pair_character_eq_finrank : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W), _root_.GlobalTheory.BI.pair (fun g => algebraMap K L (σ.character g)) (fun g => algebraMap K L (ρ.character g)) = (Module.finrank K (Representation.IntertwiningMap ρ σ) : L) := by sorry
