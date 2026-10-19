-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualInfinityPlaceCenters_infinityPlace_eq_actualPlaceOfPoint
-- name    : MazurTransfer.Order13ActualInfinityPlaceCenters.infinityPlace_eq_actualPlaceOfPoint
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T13:15:19.903191+00:00
-- url     : https://prove2.me/theorems/67a3ca1a-cb76-42a6-b994-2cc0f8f3b529
-- title:
--   Actual infinity localization places equal the canonical literal section places
-- statement:
--   For $a\in\mathbb Q$ with $a^2=1$, let $v_a$ be the place defined by the actual reciprocal localization and let $s_a$ be the literal infinity section of the order-13 curve. Then $$v_a=v_{s_a}.$$ This identifies the computed local Pell orders with the canonical section places in the same rational scheme function field.
-- source:
--   Original complete infinityPlace_eq_actualPlaceOfPoint statement and proof from MazurTheorem Order13ActualInfinityPlaceCenters.lean, Apache-2.0, Vas and contributors. Its original nine-line range comparison is retained as a helper in an explicit fresh namespace. Public imports and namespace context supply the dependencies. The original complete closed type is kernel-compared. Named downstream consumer: the actual degree-19 Pell principal divisor.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the two reciprocal-localization places with the
canonical places centered at the two literal rational infinity sections.
Named downstream consumer: the actual degree-19 Pell principal divisor.
The actual stalk diagram supplies the identification, rather than a supplied
valuation equivalence or a substituted abstract curve.
-/
import Definitions.Def_MazurTransfer_Order13ActualInfinitySectionCenterCertificates
noncomputable section
open MazurTransfer AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityLocalParameter Order13ReciprocalChartActualFunctionField
open Order13PellActualInfinityValuations Order13IntegralSections Order13RationalSectionPicardInjection Order13ActualInfinityPlaceCenters
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.Order13ActualInfinityPlaceCenters.infinityPlace_eq_actualPlaceOfPoint (a : ℚ) (ha : a ^ 2 = 1) :
    infinityPlace a ha = actualPlaceOfPoint ℚ (sectionClosedPoint ℚ (infinitySection ℚ a ha)) := by sorry
