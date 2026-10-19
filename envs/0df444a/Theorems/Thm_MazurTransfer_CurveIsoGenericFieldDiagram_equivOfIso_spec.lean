-- Prove2me | Theorems.Thm_MazurTransfer_CurveIsoGenericFieldDiagram_equivOfIso_spec
-- name    : MazurTransfer.CurveIsoGenericFieldDiagram.equivOfIso_spec
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T13:04:00.127168+00:00
-- url     : https://prove2.me/theorems/d18dbee7-43e0-435c-967f-1f73390acf47
-- title:
--   Curve-isomorphism function-field pullback commutes with the generic-stalk embedding
-- statement:
--   For any isomorphism between integral schemes in the same universe, the original function-field ring equivalence induced by generic-stalk pullback commutes with the actual generic-stalk maps from spectra.
-- source:
--   MazurTheorem CurveIsoGenericFieldDiagram.equivOfIso_spec. The original explicit function-field pullback helpers are complete official Anthropic FLT source at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the complete checked FLT function-field pullback associated
to a curve isomorphism commutes with its actual generic-stalk embedding.
Named downstream consumer: Order13ActualGeometricGaloisSemilinearAutomorphism.
-/
import Definitions.Def_MazurTransfer_CurveModelGeometricSemilinearLiftOriginalData20261018

noncomputable section
universe u
open MazurTransfer.CurveModelGeometricSemilinearLiftOriginalData20261018.FunctionFieldPull
open CategoryTheory AlgebraicGeometry

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem MazurTransfer.CurveIsoGenericFieldDiagram.equivOfIso_spec (e : X ≅ Y) :
    Spec.map (CommRingCat.ofHom (equivOfIso e).toRingHom) ≫
        Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ e.hom := by sorry
