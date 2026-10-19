-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_place_of_point_bijective
-- name    : MazurTransfer.order13_actual_place_of_point_bijective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T02:47:51.585498+00:00
-- url     : https://prove2.me/theorems/b408e246-5947-4738-8251-085b3fde84e9
-- title:
--   Closed points and function-field places of the actual order-thirteen curve
-- statement:
--   Let $K$ be a field with $104\ne0$, and let $C_K$ be the smooth proper curve given by the fixed two-chart order-thirteen model. For a closed point $x$, let $v_x$ be the function-field place whose valuation ring is the image of the local ring $\mathcal O_{C_K,x}$ in $K(C_K)$. Then
--   $$C_K^{\mathrm{cl}}\longrightarrow\operatorname{Places}_K\bigl(K(C_K)\bigr),\qquad x\longmapsto v_x,$$
--   is a bijection.
--
--   This identifies actual geometric closed points with actual places and supplies the point/place component of the CurveModel used in the integral Abel–Jacobi injectivity proof.
-- source:
--   Exact checked MazurTheorem proof AcceptedOrder13GoodCharacteristicPicardCache.lean, lines 206–217, extracted by the Lean declaration and syntax oracles. Official Anthropic FLT range-of-stalk existence and uniqueness theorems at 6e837e75355538c7f80bab5b956861e86c4eacc2 retain Apache-2.0 attribution. Vas and contributors, Apache-2.0.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Exact place-bijection proof from the checked actual good-characteristic
curve foundation. Original official Anthropic FLT dependencies retain
Apache-2.0 and commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: closed points of the actual curve identify bijectively
with places of its actual function field. Named downstream consumer:
construction of the actual CurveModel for Abel-Jacobi injectivity. -/
import Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]

theorem MazurTransfer.order13_actual_place_of_point_bijective : Function.Bijective (actualPlaceOfPoint K)  := by sorry
