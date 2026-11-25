-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_natDegree_originPolynomial
-- name    : GlobalTheory.WeierstrassCurve.natDegree_originPolynomial
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:32.993815+00:00
-- url     : https://prove2.me/theorems/92798078-928d-458e-b288-13c0553171ae
-- title:
--   Weierstrass Curve: nat Degree origin Polynomial
-- statement:
--   The Weierstrass Curve construction uses the nat Degree origin Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L681-L683
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L681-L683

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

theorem GlobalTheory.WeierstrassCurve.natDegree_originPolynomial [Nontrivial R] : (originPolynomial W).natDegree = 3 := by sorry
