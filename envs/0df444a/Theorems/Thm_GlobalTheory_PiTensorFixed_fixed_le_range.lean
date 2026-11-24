-- Prove2me | Theorems.Thm_GlobalTheory_PiTensorFixed_fixed_le_range
-- name    : GlobalTheory.PiTensorFixed.fixed_le_range
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:48:52.958587+00:00
-- url     : https://prove2.me/theorems/f66dbffc-23c7-4d88-9996-1d9bd1cf7ee7
-- title:
--   Pi Tensor Fixed: fixed le range
-- statement:
--   The Pi Tensor Fixed construction uses the fixed le range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalCompactFixedVectorsPiTensorSmoo.lean#L53-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalCompactFixedVectorsPiTensorSmoo.lean#L53-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalCompactFixedVectorsPiTensorSmoo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
open GlobalTheory GlobalTheory.PiTensorFixed
variable {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)]
  [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

theorem GlobalTheory.PiTensorFixed.fixed_le_range (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (hρ : ∀ a, IsSmooth (ρ a))
    (K : ∀ a, Subgroup (Γ a)) (hK : ∀ a, IsCompact (K a : Set (Γ a))) :
    fixed (piTensor ρ) (Subgroup.pi Set.univ K) ≤
      LinearMap.range (PiTensorProduct.map fun a => (fixed (ρ a) (K a)).subtype) := by sorry
