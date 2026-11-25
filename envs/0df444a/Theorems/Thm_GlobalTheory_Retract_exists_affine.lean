-- Prove2me | Theorems.Thm_GlobalTheory_Retract_exists_affine
-- name    : GlobalTheory.Retract.exists_affine
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:19:46.758867+00:00
-- url     : https://prove2.me/theorems/db656e06-0575-4f4d-9c31-e856acfb8f0f
-- title:
--   Retract: exists affine
-- statement:
--   The Retract construction uses the exists affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L109-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L109-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {i : X ⟶ Y} {r : Y ⟶ X}

theorem GlobalTheory.Retract.exists_affine (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g) (x : X) :
    ∃ (U : X.Opens) (V : Y.Opens) (W : S.Opens),
      IsAffineOpen U ∧ IsAffineOpen V ∧ IsAffineOpen W ∧ x ∈ U ∧
      U ≤ i ⁻¹ᵁ V ∧ V ≤ r ⁻¹ᵁ U ∧ U ≤ f ⁻¹ᵁ W ∧ V ≤ g ⁻¹ᵁ W := by sorry
