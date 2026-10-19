-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualCurveInversePlaceSet_inverse_placesOf
-- name    : MazurTransfer.Order13ActualCurveInversePlaceSet.inverse_placesOf
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T14:43:38.048447+00:00
-- url     : https://prove2.me/theorems/4b1469ee-804e-41e1-b8fc-f3c69cda98c4
-- title:
--   Inverse curve preimages transport the actual closed-point place sets by the field automorphism
-- statement:
--   Let $F$ be the existing rational scheme function field of the literal order-13 curve. For every $\mathbb Q$-automorphism $\sigma$ of $F$, let $g_\sigma$ be the inverse morphism of its original specified generic-compatible curve lift. Every open $U$ satisfies $$\operatorname{Places}(g_\sigma^{-1}U)=\sigma\operatorname{Places}(U),$$ where the inverse on the open denotes preimage. This supplies the exact place-set compatibility for arithmetic divisor-presentation pullback.
-- source:
--   Original complete inverse_placesOf statement and proof, with original mem_placesOf_actual_iff helper, from MazurTheorem Order13ActualCurveInversePlaceSet.lean, Apache-2.0, Vas and contributors. Public original generic curve-lift order/inverse data, actual closed-point images and place definitions supply dependencies. The complete original type is kernel-compared after bounded expansion only of missing original module-local instances. The original local rational function-field algebra type and value are independently compared with the closed existing public provider actualCurveFunctionFieldAlgebra ℚ. Named downstream consumer: Order13ActualCurveDivisorPresentationPullback.presentation_pullback.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inverse-curve preimages of opens transport the literal
sets of closed-point valuation places by the field automorphism. Named
downstream consumer: the range condition for transformed divisor presentations.
-/
import Definitions.Def_MazurTransfer_Order13ActualDiamondGenericCurveOrder
import Definitions.Def_MazurTransfer_Order13ActualDiamondCurveAutomorphism
import Definitions.Def_AlgebraicCurve_PlacesOf
noncomputable section
open MazurTransfer

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualCurveFieldAutomorphismLift Order13ActualDiamondGenericCurveOrder
open Order13ActualDiamondCurveAutomorphism
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ F := actualCurveFunctionFieldAlgebra ℚ

theorem MazurTransfer.Order13ActualCurveInversePlaceSet.inverse_placesOf (σ : F ≃ₐ[ℚ] F) (U : C.Opens) :
    placesOf (curveToBase ℚ) ((fieldLift σ).inv ⁻¹ᵁ U) =
      (fun v : Place ℚ F => σ • v) '' placesOf (curveToBase ℚ) U := by sorry
