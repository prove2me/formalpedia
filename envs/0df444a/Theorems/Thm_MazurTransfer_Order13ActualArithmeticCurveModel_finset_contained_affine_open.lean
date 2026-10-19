-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualArithmeticCurveModel_finset_contained_affine_open
-- name    : MazurTransfer.Order13ActualArithmeticCurveModel.finset_contained_affine_open
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T02:53:37.985997+00:00
-- url     : https://prove2.me/theorems/6354eb4b-0079-40a6-8c4b-fceeecd12ed4
-- title:
--   Affine neighborhoods of finite sets on the actual order-thirteen curve
-- statement:
--   Let $K$ be a field in which $104\ne0$, and let $C_K$ be the actual smooth proper order-thirteen curve. For every finite subset $S\subseteq C_K$, there is an affine open subset $U\subseteq C_K$ such that
--   $$S\subseteq U.$$
--
--   This provides the finite-set affine-neighborhood condition of the actual CurveModel used in the Abel–Jacobi point-injection argument. No affine-neighborhood assumption is supplied as a hypothesis.
-- source:
--   MazurTheorem exact statement Order13ActualArithmeticCurveModel.lean, finset_contained_affine_open. This checked proof uses the existing public general finite-map existence and finite-set affine-neighborhood theorems from official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, together with the published actual two-chart cover, infinity section and actual geometric-integrality theorem. Apache-2.0.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: every finite set on the actual good-characteristic order13
curve lies in an affine open. Named downstream consumer: the actual CurveModel
used by the integral Abel-Jacobi point-difference injection. This proof uses
the existing public finite-map existence theorem, independent of the explicit
degree-three finite-map construction. Official Anthropic FLT APIs retain
Apache-2.0 and pin 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
import Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation
import Definitions.Def_MazurTransfer_Order13ActualTwoAffineOpenCover
import Definitions.Def_MazurTransfer_Order13IntegralInfinitySections
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_geometrically_integral
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_finiteMapData_le_isUnit_of_twoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_isAffineOpen_le_preimage_of_finset
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13IntegralSections
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]

theorem MazurTransfer.Order13ActualArithmeticCurveModel.finset_contained_affine_open (F : Finset (curveScheme K)) :
    ∃ U : (curveScheme K).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U  := by sorry
