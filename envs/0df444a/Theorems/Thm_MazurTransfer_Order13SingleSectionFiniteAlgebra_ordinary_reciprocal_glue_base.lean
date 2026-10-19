-- Prove2me | Theorems.Thm_MazurTransfer_Order13SingleSectionFiniteAlgebra_ordinary_reciprocal_glue_base
-- name    : MazurTransfer.Order13SingleSectionFiniteAlgebra.ordinary_reciprocal_glue_base
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T06:14:58.48055+00:00
-- url     : https://prove2.me/theorems/0c484b40-e47a-4d42-a2ea-bfc56b3569bc
-- title:
--   The actual ordinary and reciprocal chart maps agree on their literal overlap
-- statement:
--   Let $R$ be a commutative ring, let $A$ and $A^\vee$ be the ordinary and reciprocal coordinate rings of the actual order-thirteen curve $C$, and let $A_x$ be the ordinary overlap ring. The localization map $A\to A_x$ and the retained reciprocal-to-ordinary map $A^\vee\to A_x$ induce the same morphism to the glued curve: $$\operatorname{Spec}(A_x)\longrightarrow C.$$ This is the actual overlap identity needed to glue the inverse finite-coordinate atlas to $C$, with no domain or invertibility assumptions.
-- source:
--   Original ordinary_reciprocal_glue_base theorem from MazurTheorem Order13SingleSectionCurveOverlapCompatibility.lean, Apache-2.0, Vas and contributors. The eleven-line proof is unchanged apart from renaming its inline helper namespace to avoid a transitive native-cache collision. The original ten-line ordinary_reciprocal_glue helper is explicitly retained in the submitted source; no transitive helper is used as a public theorem. Original and public full types are compared in the kernel. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: actual inverse finite-chart overlap compatibility.

import Mathlib
import Definitions.Def_MazurTransfer_Order13CanonicalFiniteMapPrimitiveScopes
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer
universe u

theorem MazurTransfer.Order13SingleSectionFiniteAlgebra.ordinary_reciprocal_glue_base (R : Type u) [CommRing R] :
    Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R))) ≫
      ordinaryChartMap R =
    Spec.map (CommRingCat.ofHom (reciprocalToOrdinaryBase R).toRingHom) ≫ reciprocalChartMap R := by sorry
