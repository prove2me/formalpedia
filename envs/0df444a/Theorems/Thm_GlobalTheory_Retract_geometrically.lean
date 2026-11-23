-- Prove2me | Theorems.Thm_GlobalTheory_Retract_geometrically
-- name    : GlobalTheory.Retract.geometrically
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:49.267644+00:00
-- url     : https://prove2.me/theorems/970c9e7a-fc10-4efb-aa3e-4ab37e052f8e
-- title:
--   Retract: geometrically
-- statement:
--   The Retract construction uses the geometrically property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L323-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L323-L328

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
  (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
include hir hr

theorem GlobalTheory.Retract.geometrically (P : ObjectProperty Scheme.{u})
    (hP : ∀ {A B : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ A), a ≫ b = 𝟙 A → P B → P A)
    (hg : AlgebraicGeometry.geometrically P g) : AlgebraicGeometry.geometrically P f := by sorry
