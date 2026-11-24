-- Prove2me | Theorems.Thm_GlobalTheory_T_finiteDimensional_compact_fixed_vectors_piTensor_smooth
-- name    : GlobalTheory.T.finiteDimensional_compact_fixed_vectors_piTensor_smooth
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:39:42.490792+00:00
-- url     : https://prove2.me/theorems/27aecf5d-86e8-40cb-9319-d182345d4184
-- title:
--   T: finite Dimensional compact fixed vectors pi Tensor smooth
-- statement:
--   The T construction uses the finite Dimensional compact fixed vectors pi Tensor smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalCompactFixedVectorsPiTensorSmooStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalCompactFixedVectorsPiTensorSmooStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalCompactFixedVectorsPiTensorSmoo
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalCompactFixedVectorsPiTensorSmooStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finiteDimensional_compact_fixed_vectors_piTensor_smooth : ∀ {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)), (∀ a, IsSmooth (ρ a)) → ∀ (K : ∀ a, Subgroup (Γ a)), (∀ a, IsCompact (K a : Set (Γ a))) → (∀ a, FiniteDimensional ℂ (fixed (ρ a) (K a))) → FiniteDimensional ℂ (fixed (piTensor ρ) (Subgroup.pi Set.univ K)) := by sorry
