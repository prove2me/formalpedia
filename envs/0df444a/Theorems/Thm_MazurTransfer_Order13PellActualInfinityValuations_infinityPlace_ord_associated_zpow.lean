-- Prove2me | Theorems.Thm_MazurTransfer_Order13PellActualInfinityValuations_infinityPlace_ord_associated_zpow
-- name    : MazurTransfer.Order13PellActualInfinityValuations.infinityPlace_ord_associated_zpow
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T12:12:29.031142+00:00
-- url     : https://prove2.me/theorems/3814f365-dc69-446c-ad72-69a73cd02a79
-- title:
--   Actual infinity order of an element associated to a uniformizer power
-- statement:
--   Let $a\in\mathbb Q$ satisfy $a^2=1$, let $b$ lie in the actual local ring at the reciprocal-chart point $(0,a)$, and let $n\in\mathbb N$. If $b$ is associated to $z^n$ in that local ring, its image in the existing scheme function field satisfies $$b\sim z^n\quad\Longrightarrow\quad\operatorname{ord}_{v_a}(b)=n.$$ This is the original comparison used for the non-unit Pell factor and its exact infinity order.
-- source:
--   Original complete infinityPlace_ord_associated_zpow statement and proof from MazurTheorem Order13PellActualInfinityValuations.lean, Apache-2.0, Vas and contributors. The complete original statement and main body are unchanged. Public imports and top-level namespace context alone are replaced. Native, strict and complete frontend checks pass; complete original and public closed types are kernel-compared. Named downstream consumer: actual Pell function order at negative infinity.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two actual reciprocal localizations define genuine
places of the literal rational scheme function field, and z has order one.
Named downstream consumer: the Pell principal-divisor formula on that field.
The identification with the two infinity section centers is separate work.
-/
import Definitions.Def_MazurTransfer_Order13ActualInfinityValuationData
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

theorem MazurTransfer.Order13PellActualInfinityValuations.infinityPlace_ord_associated_zpow (a : ℚ) (ha : a ^ 2 = 1)
    (b : LocalRing ℚ a ha) (n : ℕ) (hb : Associated b (z ℚ a ha ^ n)) :
    (infinityPlace a ha).ord (algebraMap (LocalRing ℚ a ha) (actualCurveFunctionField ℚ) b) = n := by sorry
