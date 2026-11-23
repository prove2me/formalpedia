-- Prove2me | Theorems.Thm_GlobalTheory_Retract_section_comp
-- name    : GlobalTheory.Retract.section_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:40.52529+00:00
-- url     : https://prove2.me/theorems/ef3d9201-aa59-474f-986e-1fd2c70ad92a
-- title:
--   Retract: section comp
-- statement:
--   The Retract construction uses the section comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L82-L83

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

theorem GlobalTheory.Retract.section_comp (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g) : i ≫ g = f := by sorry
