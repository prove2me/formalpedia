-- Prove2me | Theorems.Thm_GlobalTheory_geometricallyConnected_of_smooth_of_section
-- name    : GlobalTheory.geometricallyConnected_of_smooth_of_section
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:54:37.949806+00:00
-- url     : https://prove2.me/theorems/5c357489-743b-4fe9-a208-bfb087121e3e
-- title:
--   Global Theory: geometrically Connected of smooth of section
-- statement:
--   The Global Theory construction uses the geometrically Connected of smooth of section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GeometricallyConnectedOfSmoothOfSection.lean#L8-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GeometricallyConnectedOfSmoothOfSection.lean#L8-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfRatPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeometricallyConnectedOfSmoothOfSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory

theorem GlobalTheory.geometricallyConnected_of_smooth_of_section :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
      (e : Spec (CommRingCat.of k) ⟶ X),
      Smooth f → e ≫ f = 𝟙 _ → ConnectedSpace X → GeometricallyConnected f := by sorry
