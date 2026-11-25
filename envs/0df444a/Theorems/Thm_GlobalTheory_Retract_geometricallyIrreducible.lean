-- Prove2me | Theorems.Thm_GlobalTheory_Retract_geometricallyIrreducible
-- name    : GlobalTheory.Retract.geometricallyIrreducible
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:19:55.567037+00:00
-- url     : https://prove2.me/theorems/4ee75ccb-b530-4662-8706-1e376813c108
-- title:
--   Retract: geometrically Irreducible
-- statement:
--   The Retract construction uses the geometrically Irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L333-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L333-L334

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

theorem GlobalTheory.Retract.geometricallyIrreducible [hg : GeometricallyIrreducible g] : GeometricallyIrreducible f := by sorry
