-- Prove2me | Theorems.Thm_MazurTransfer_affine_chart_coordinate_embedding_base_scalars
-- name    : MazurTransfer.affine_chart_coordinate_embedding_base_scalars
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T17:07:25.050021+00:00
-- url     : https://prove2.me/theorems/baadf6da-fe95-4d63-919d-301cd92bb63f
-- title:
--   The canonical affine-chart function-field embedding respects base scalars
-- statement:
--   For an integral scheme over a field K, an integral affine open chart Spec A whose structural map is compatible with the K-algebra structure has a canonical coordinate embedding into the existing scheme function field. The embedding constructed from the generic-point stalk isomorphism sends the scalar image of every r in K to the curve structural scalar image. This specifies the actual embedding, without introducing an algebra equivalence hypothesis. The named downstream consumer is the order-thirteen diamond field automorphism over every characteristic-zero extension field, followed by geometric base-change compatibility of its Picard action.
-- source:
--   Owned MazurTheorem integration proof using Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474 and the original Apache-2.0 Anthropic FLT baseToFunctionField definition at 6e837e75355538c7f80bab5b956861e86c4eacc2: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_CurveModel.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u

theorem MazurTransfer.affine_chart_coordinate_embedding_base_scalars
    {K : Type u} [Field K] (A : CommRingCat.{u}) [IsDomain A] [Algebra K A]
    {C : Scheme.{u}} [IsIntegral C] (c : C ⟶ Spec (CommRingCat.of K))
    (j : Spec A ⟶ C) [IsOpenImmersion j]
    (hc : j ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A))) (r : K) :
    let e : C.functionField ≅ (Spec A).functionField :=
      eqToIso (congrArg C.presheaf.stalk (genericPoint_eq_of_isOpenImmersion j).symm) ≪≫
        asIso (j.stalkMap (genericPoint (Spec A)))
    e.inv.hom (algebraMap A (Spec A).functionField (algebraMap K A r)) = baseToFunctionField c r := by sorry
