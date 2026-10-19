-- Prove2me | Theorems.Thm_MazurTransfer_Order13PellActualOrdinaryChart_pellFunction_eq_ordinaryPlus
-- name    : MazurTransfer.Order13PellActualOrdinaryChart.pellFunction_eq_ordinaryPlus
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T13:49:35.009165+00:00
-- url     : https://prove2.me/theorems/4ad19970-3683-40e9-8c2a-d1822ce4620d
-- title:
--   The actual infinity-defined Pell function equals the ordinary coordinate unit
-- statement:
--   In the existing rational scheme function field of the literal order-13 curve, let $f$ be the specified reciprocal expression for the Pell function. Its value equals the original ordinary factor: $$f=\iota_o\bigl(H(x)+yK(x)\bigr).$$ The ordinary factor is a proved unit. This equality transfers that unit certificate to zero-order calculations at ordinary-chart points.
-- source:
--   Original complete pellFunction_eq_ordinaryPlus statement and proof from MazurTheorem Order13PellActualOrdinaryChart.lean, Apache-2.0, Vas and contributors. Public original Pell chart identities and actual infinity valuation data supply all dependencies. The full original closed type is kernel-compared. Named downstream consumer: Pell orders vanish at every ordinary-chart closed point.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the actual infinity-defined Pell function with
the ordinary-coordinate unit using the literal chart overlap. Named downstream
consumer: vanishing orders at all places in the ordinary affine chart.
-/
import Definitions.Def_MazurTransfer_Order13PellChartOverlapIdentities
import Definitions.Def_MazurTransfer_Order13ActualInfinityValuationData
noncomputable section
universe u
open MazurTransfer
open Order13PellActualOrdinaryChart
open AlgebraicGeometry CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellChartCertificate Order13ChartOverlapFunctionField
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.Order13PellActualOrdinaryChart.pellFunction_eq_ordinaryPlus :
    Order13PellActualInfinityValuations.pellFunction =
      algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ) (ordinaryPlus ℚ) := by sorry
