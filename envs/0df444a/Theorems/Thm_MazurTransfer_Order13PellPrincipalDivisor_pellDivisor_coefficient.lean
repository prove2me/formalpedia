-- Prove2me | Theorems.Thm_MazurTransfer_Order13PellPrincipalDivisor_pellDivisor_coefficient
-- name    : MazurTransfer.Order13PellPrincipalDivisor.pellDivisor_coefficient
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T14:30:41.027054+00:00
-- url     : https://prove2.me/theorems/ccbd5430-bf3c-45b8-bc8a-feaeef71c206
-- title:
--   The specified Pell function has exactly the original two-point divisor
-- statement:
--   For every place $v$ of the existing rational scheme function field of the literal order-13 curve, the specified divisor $D=19[v_-]-19[v_+]$ and original Pell function $f$ satisfy $$D(v)=\operatorname{ord}_v(f).$$ This gives the complete divisor formula for that actual function, with its canonical infinity places.
-- source:
--   Original complete pellDivisor_coefficient statement and proof from MazurTheorem Order13PellPrincipalDivisor.lean, Apache-2.0, Vas and contributors. The unchanged original divisor and Pell function constructors are supplied by published Definitions. Public proved infinity orders and global orders away from infinity supply the complete valuation input. The full original closed type is kernel-compared. Named downstream consumer: the original Pell principal-divisor certificate and exact order nineteen of the actual infinity class.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact two-point principal divisor of the explicit Pell
function in the actual rational scheme function field. Named downstream
consumer: nineteen annihilates the difference of the infinity Picard classes.
-/
import Definitions.Def_MazurTransfer_Order13PellPrincipalDivisorData
import Definitions.Def_MazurTransfer_Order13PellChartOverlapIdentities
import Theorems.Thm_MazurTransfer_Order13PellPrincipalDivisor_pellFunction_ord_away_infinity
import Theorems.Thm_MazurTransfer_Order13PellActualOrdinaryChart_pellFunction_eq_ordinaryPlus
noncomputable section
open MazurTransfer
open Order13PellPrincipalDivisor
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13IntegralSections Order13RationalSectionPicardInjection Order13ActualInfinityPlaceCenters
open Order13PellActualInfinityValuations
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.Order13PellPrincipalDivisor.pellDivisor_coefficient (v : Place ℚ (actualCurveFunctionField ℚ)) :
    pellDivisor v = v.ord pellFunction := by sorry
