-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_chartZ_eq
-- name    : GlobalTheory.WeierstrassCurve.chartZ_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:04.816477+00:00
-- url     : https://prove2.me/theorems/72331434-9a54-5ab2-8fd1-17910e7ce9ab
-- title:
--   Weierstrass Curve: chart Z eq
-- statement:
--   The Weierstrass Curve construction uses the chart Z eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L662-L664
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L662-L664

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal Limits
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
open Polynomial
open scoped Polynomial.Bivariate
variable {A : Type*} [CommRing A]

theorem GlobalTheory.WeierstrassCurve.chartZ_eq : chartZ W = Spec.map (CommRingCat.ofHom
    (awayEquivAffine W : AwayRing W 2 →+* W.toAffine.CoordinateRing)) ≫ awayChart W 2 := by sorry
