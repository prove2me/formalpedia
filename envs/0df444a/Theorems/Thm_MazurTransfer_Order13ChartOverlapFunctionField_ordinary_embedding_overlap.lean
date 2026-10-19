-- Prove2me | Theorems.Thm_MazurTransfer_Order13ChartOverlapFunctionField_ordinary_embedding_overlap
-- name    : MazurTransfer.Order13ChartOverlapFunctionField.ordinary_embedding_overlap
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T13:41:27.828876+00:00
-- url     : https://prove2.me/theorems/8b789c5b-9e69-421f-bd7b-e3e0b7d7f3b2
-- title:
--   The actual ordinary coordinate embedding agrees with the reciprocal overlap embedding
-- statement:
--   Over a characteristic-zero field $K$, let $A_o$ be the ordinary coordinate ring of the literal order-13 curve, and let $A_{r,z}$ be its reciprocal overlap ring. If $\tau:A_o\to A_{r,z}$ is the original coordinate transition and $e$ is the specified overlap embedding into the existing scheme function field, then $$\iota_o(b)=e(\tau(b))\qquad(b\in A_o).$$ This identifies the original ordinary and reciprocal coordinates in the same function field.
-- source:
--   Original complete ordinary_embedding_overlap statement and proof from MazurTheorem Order13ChartOverlapFunctionField.lean, Apache-2.0, Vas and contributors. The original three-line general restriction-with-equality consequence is retained in an explicit fresh helper namespace. Public proved affine restriction and actual chart-map gluing supply the original dependencies. The full original closed type is kernel-compared. Named downstream consumer: actual Pell ordinary unit expression.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal gluing transition identifies the two affine
coordinate embeddings in the actual scheme function field. Named downstream
consumer: the ordinary-chart expression for the Pell function.
-/
import Definitions.Def_MazurTransfer_Order13ChartOverlapEmbeddingData
import Theorems.Thm_MazurTransfer_Order13ChartOverlapFunctionField_overlap_chart_maps_agree
import Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldNaturality_coordinate_embedding_restriction
noncomputable section
universe u
open MazurTransfer
open Order13ChartOverlapFunctionField
open AlgebraicGeometry CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open AffineOpenChartFunctionField AffineOpenChartFunctionFieldNaturality
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.Order13ChartOverlapFunctionField.ordinary_embedding_overlap (b : CoordinateRing K) :
    algebraMap (CoordinateRing K) (actualCurveFunctionField K) b =
      overlapEmbedding K (ordinaryToReciprocalBase K b) := by sorry
