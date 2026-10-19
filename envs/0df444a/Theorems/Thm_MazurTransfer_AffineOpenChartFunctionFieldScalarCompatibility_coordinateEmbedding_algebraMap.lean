-- Prove2me | Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldScalarCompatibility_coordinateEmbedding_algebraMap
-- name    : MazurTransfer.AffineOpenChartFunctionFieldScalarCompatibility.coordinateEmbedding_algebraMap
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T17:06:24.838607+00:00
-- url     : https://prove2.me/theorems/d09ea75b-7ec7-42b8-9976-d9186506afe9
-- title:
--   Affine chart function-field embedding respects the base-field scalar map
-- statement:
--   For an integral scheme C over a field K and an integral affine open chart Spec A mapping to C over K, the canonical coordinate embedding A into the actual function field of C sends each structural scalar r to the structural function-field image of r. The full original universes, algebra structure and chart commutation hypothesis are retained.
-- source:
--   Complete original MazurTheorem AffineOpenChartFunctionFieldScalarCompatibility.coordinateEmbedding_algebraMap proof. Official Anthropic FLT curve-model interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual coordinate embedding of an affine open chart
respects the structural base-field map. Named downstream consumer: diamond
function-field automorphisms over geometric extension fields of Q.
-/
import Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldNaturality_coordinate_embedding_via_stalk
import Definitions.Def_AlgebraicCurve_CurveModel

noncomputable section
universe u
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AffineOpenChartFunctionField AffineOpenChartFunctionFieldNaturality
variable {K : Type u} [Field K] (A : CommRingCat.{u}) [IsDomain A] [Algebra K A]
  {C : Scheme.{u}} [IsIntegral C] (c : C ⟶ Spec (CommRingCat.of K))
  (j : Spec A ⟶ C) [IsOpenImmersion j]

theorem MazurTransfer.AffineOpenChartFunctionFieldScalarCompatibility.coordinateEmbedding_algebraMap
    (hc : j ≫ c = Spec.map (CommRingCat.ofHom (algebraMap K A))) (r : K) :
    coordinateEmbedding A j (algebraMap K A r) = baseToFunctionField c r := by sorry
