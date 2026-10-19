-- Prove2me | Theorems.Thm_MazurTransfer_Order13ChartOverlapFunctionField_overlap_chart_maps_agree
-- name    : MazurTransfer.Order13ChartOverlapFunctionField.overlap_chart_maps_agree
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T13:34:23.670293+00:00
-- url     : https://prove2.me/theorems/2665a644-c94e-48ef-97ec-f49c4fd3b013
-- title:
--   The actual ordinary and reciprocal overlap maps agree on the glued order-13 curve
-- statement:
--   For every characteristic-zero field $K$, the two specified morphisms from the reciprocal overlap chart to the literal order-13 curve coincide: the ordinary chart composed with the original coordinate transition equals the reciprocal chart composed with localization. This is the actual gluing equality for the original charts and their specified maps.
-- source:
--   Original complete overlap_chart_maps_agree statement and proof from MazurTheorem Order13ChartOverlapFunctionField.lean, Apache-2.0, Vas and contributors. Public original overlap data and the proved cast-free gluing condition supply its dependencies. The full original closed type is kernel-compared. Named downstream consumer: the actual ordinary and reciprocal coordinate embeddings agree in the same scheme function field.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal gluing transition identifies the two affine
coordinate embeddings in the actual scheme function field. Named downstream
consumer: the ordinary-chart expression for the Pell function.
-/
import Definitions.Def_MazurTransfer_Order13ChartOverlapEmbeddingData
import Theorems.Thm_MazurTransfer_GlueDataPrimeOverlapCompatibility_glue_condition
noncomputable section
universe u
open MazurTransfer
open Order13ChartOverlapFunctionField
open AlgebraicGeometry CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open AffineOpenChartFunctionField
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.Order13ChartOverlapFunctionField.overlap_chart_maps_agree :
    Spec.map (CommRingCat.ofHom (ordinaryToReciprocalBase K).toRingHom) ≫
        ordinaryChartMap K =
      Spec.map (CommRingCat.ofHom
        (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K))) ≫ reciprocalChartMap K := by sorry
