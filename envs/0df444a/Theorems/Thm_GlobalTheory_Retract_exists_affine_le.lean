-- Prove2me | Theorems.Thm_GlobalTheory_Retract_exists_affine_le
-- name    : GlobalTheory.Retract.exists_affine_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:38.37229+00:00
-- url     : https://prove2.me/theorems/d6418972-287c-4bce-9435-2ca88b0235ce
-- title:
--   Retract: exists affine le
-- statement:
--   The Retract construction uses the exists affine le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L88-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L88-L107

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

theorem GlobalTheory.Retract.exists_affine_le (hir : i ≫ r = 𝟙 X) (x : X) (O : X.Opens) (hx : x ∈ O) :
    ∃ (U : X.Opens) (V : Y.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ x ∈ U ∧ U ≤ O ∧
      U ≤ i ⁻¹ᵁ V ∧ V ≤ r ⁻¹ᵁ U := by sorry
