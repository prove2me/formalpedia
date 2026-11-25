-- Prove2me | Theorems.Thm_GlobalTheory_Retract_geometricallyIntegral
-- name    : GlobalTheory.Retract.geometricallyIntegral
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:19:51.896803+00:00
-- url     : https://prove2.me/theorems/331d7648-d69d-5186-9bd7-b6e452eb87a2
-- title:
--   Retract: geometrically Integral
-- statement:
--   The Retract construction uses the geometrically Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L339-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L339-L340

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

theorem GlobalTheory.Retract.geometricallyIntegral [hg : GeometricallyIntegral g] : GeometricallyIntegral f := by sorry
