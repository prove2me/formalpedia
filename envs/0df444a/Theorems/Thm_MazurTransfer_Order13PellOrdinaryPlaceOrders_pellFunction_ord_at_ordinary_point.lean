-- Prove2me | Theorems.Thm_MazurTransfer_Order13PellOrdinaryPlaceOrders_pellFunction_ord_at_ordinary_point
-- name    : MazurTransfer.Order13PellOrdinaryPlaceOrders.pellFunction_ord_at_ordinary_point
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T13:57:08.20199+00:00
-- url     : https://prove2.me/theorems/fa4534d6-0d0a-43d8-8517-c04ade44265b
-- title:
--   The actual Pell function has order zero at every ordinary-chart closed point
-- statement:
--   Let $x$ be a closed point of the literal order-13 curve over $\mathbb Q$, and let $p$ be an ordinary-chart point with $j_o(p)=x$. At the canonical place $v_x$ of the existing scheme function field, the specified Pell function satisfies $$\operatorname{ord}_{v_x}(f)=0.$$ This excludes every ordinary-chart place from its divisor support.
-- source:
--   Original complete pellFunction_ord_at_ordinary_point statement and proof from MazurTheorem Order13PellOrdinaryPlaceOrders.lean, Apache-2.0, Vas and contributors. Public original Pell chart identities, the proved actual ordinary unit expression, the canonical affine stalk factorization and the proved unit-to-order-zero theorem supply all dependencies. The full original closed type is kernel-compared. Named downstream consumer: the global Pell divisor is supported at the two literal infinity places.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: at a closed point in the actual ordinary chart, the Pell
function has order zero. Named downstream consumer: the global two-point
principal-divisor certificate on the rational order-13 curve.
-/
import Definitions.Def_MazurTransfer_Order13PellChartOverlapIdentities
import Definitions.Def_MazurTransfer_Order13ActualRationalSectionDegreeOneData
import Theorems.Thm_MazurTransfer_Order13PellActualOrdinaryChart_pellFunction_eq_ordinaryPlus
import Theorems.Thm_MazurTransfer_PlaceOrderOfRangeUnit_ord_image_unit
import Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldNaturality_coordinate_embedding_via_stalk
noncomputable section
open MazurTransfer
open AlgebraicGeometry CategoryTheory AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13PellChartCertificate
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.Order13PellOrdinaryPlaceOrders.pellFunction_ord_at_ordinary_point
    (p : Spec (.of (CoordinateRing ℚ)))
    (x : closedPoints (curveScheme ℚ)) (hx : ordinaryChartMap ℚ p = x.1) :
    (actualPlaceOfPoint ℚ x).ord Order13PellActualInfinityValuations.pellFunction = 0 := by sorry
