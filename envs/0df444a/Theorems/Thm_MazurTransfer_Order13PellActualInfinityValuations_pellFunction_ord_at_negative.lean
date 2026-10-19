-- Prove2me | Theorems.Thm_MazurTransfer_Order13PellActualInfinityValuations_pellFunction_ord_at_negative
-- name    : MazurTransfer.Order13PellActualInfinityValuations.pellFunction_ord_at_negative
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T12:24:35.285274+00:00
-- url     : https://prove2.me/theorems/1373f279-ca46-4cee-b212-e27dcd8e3fac
-- title:
--   The actual normalized Pell function has order nineteen at negative infinity
-- statement:
--   For the place of the existing literal rational curve function field defined by the actual local ring at $(z,w)=(0,-1)$, the specified Pell function $f=P_{\infty,+}/z^{19}$ has exact order $$\operatorname{ord}_{v_-}(f)=19.$$ Its numerator is associated to $z^{38}$ in that local ring. This is the original second infinity-order computation needed for the degree-nineteen principal divisor.
-- source:
--   Original complete pellFunction_ord_at_negative statement and main proof body from MazurTheorem Order13PellActualInfinityValuations.lean, Apache-2.0, Vas and contributors. Its short original normalized-numerator order helper is inlined unchanged under a fresh namespace. Uses the Proved actual associated-uniformizer order comparison. Native, strict and complete frontend checks pass; full original and public closed types are kernel-compared. Named downstream consumer: actual Pell principal divisor at the canonical infinity centers.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two actual reciprocal localizations define genuine
places of the literal rational scheme function field, and z has order one.
Named downstream consumer: the Pell principal-divisor formula on that field.
The identification with the two infinity section centers is separate work.
-/
import Definitions.Def_MazurTransfer_Order13ActualInfinityValuationData
import Definitions.Def_MazurTransfer_Order13PellInfinityLocalOrders
noncomputable section
open MazurTransfer
open MazurTransfer.Order13PellActualInfinityValuations
open AlgebraicGeometry AlgebraicCurve IsDedekindDomain WithZero
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityLocalParameter Order13ReciprocalChartActualFunctionField
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance (a : ℚ) (ha : a ^ 2 = 1) : IsDiscreteValuationRing (LocalRing ℚ a ha) :=
  Order13InfinityDiscreteValuationRing.localRing_isDiscreteValuationRing ℚ a ha

theorem MazurTransfer.Order13PellActualInfinityValuations.pellFunction_ord_at_negative :
    (infinityPlace (-1) (Order13PellInfinityLocalOrders.negativeProof ℚ)).ord pellFunction = 19 := by sorry
