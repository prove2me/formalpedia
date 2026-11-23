-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_isSmooth_piTensor
-- name    : GlobalTheory.SmGL.isSmooth_piTensor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:47.74015+00:00
-- url     : https://prove2.me/theorems/bb5e43a9-6096-4923-a20a-e1952552403a
-- title:
--   Sm GL: is Smooth pi Tensor
-- statement:
--   The Sm GL construction uses the is Smooth pi Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L267-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean#L267-L279

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
variable {F G H V W U : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]

theorem GlobalTheory.SmGL.isSmooth_piTensor {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module F (X a)] {ρ : ∀ a, Representation F (Γ a) (X a)} (hρ : ∀ a, IsSmooth (ρ a)) :
    IsSmooth (piTensor ρ) := by sorry
