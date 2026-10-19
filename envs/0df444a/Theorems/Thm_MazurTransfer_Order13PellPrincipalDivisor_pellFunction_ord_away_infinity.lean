-- Prove2me | Theorems.Thm_MazurTransfer_Order13PellPrincipalDivisor_pellFunction_ord_away_infinity
-- name    : MazurTransfer.Order13PellPrincipalDivisor.pellFunction_ord_away_infinity
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T14:11:50.200468+00:00
-- url     : https://prove2.me/theorems/6edf9869-dcb2-4d23-bdb2-984cd6e7b517
-- title:
--   The actual Pell function has order zero away from the two canonical infinity places
-- statement:
--   For the specified Pell function $f$ in the existing rational scheme function field of the literal order-13 curve, every place other than its canonical positive and negative infinity places satisfies $$v\ne v_+,\quad v\ne v_-\quad\Longrightarrow\quad\operatorname{ord}_v(f)=0.$$ Thus only those two literal infinity places can support its divisor.
-- source:
--   Original complete pellFunction_ord_away_infinity statement and proof from MazurTheorem Order13PellPrincipalDivisor.lean, Apache-2.0, Vas and contributors. The original three-line ordinary-range consequence from Order13PellOrdinaryPlaceOrders.lean is retained as a fresh helper. Public original actual curve-model bijection, ordinary-chart complement, Pell divisor data and proved ordinary-point order theorem provide all dependencies. The full original closed type is kernel-compared. Named downstream consumer: the exact two-point Pell principal divisor and order nineteen of the actual infinity Picard class.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact two-point principal divisor of the explicit Pell
function in the actual rational scheme function field. Named downstream
consumer: nineteen annihilates the difference of the infinity Picard classes.
-/
import Definitions.Def_MazurTransfer_Order13PellPrincipalDivisorData
import Definitions.Def_MazurTransfer_Order13ActualCurveModel
import Theorems.Thm_MazurTransfer_Order13OrdinaryChartComplement_point_in_ordinary_or_infinity
import Theorems.Thm_MazurTransfer_Order13PellOrdinaryPlaceOrders_pellFunction_ord_at_ordinary_point
noncomputable section
open MazurTransfer
open Order13PellPrincipalDivisor
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13IntegralSections Order13RationalSectionPicardInjection Order13ActualInfinityPlaceCenters
open Order13PellActualInfinityValuations Order13PellOrdinaryPlaceOrders
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.Order13PellPrincipalDivisor.pellFunction_ord_away_infinity (v : Place ℚ (actualCurveFunctionField ℚ))
    (hp : v ≠ positivePlace) (hn : v ≠ negativePlace) : v.ord pellFunction = 0 := by sorry
