-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_chartY_eq
-- name    : GlobalTheory.WeierstrassCurve.chartY_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:18.355842+00:00
-- url     : https://prove2.me/theorems/64e31350-66f5-4f26-86c1-d5e18a16b155
-- title:
--   Weierstrass Curve: chart Y eq
-- statement:
--   The Weierstrass Curve construction uses the chart Y eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L810-L812
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L810-L812

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

theorem GlobalTheory.WeierstrassCurve.chartY_eq : chartY W = Spec.map (CommRingCat.ofHom
    (awayEquivOrigin W : AwayRing W 1 →+* OriginRing W)) ≫ awayChart W 1 := by sorry
