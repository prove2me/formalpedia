-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_over_eq_toSpec
-- name    : GlobalTheory.WeierstrassCurve.over_eq_toSpec
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:46.777091+00:00
-- url     : https://prove2.me/theorems/3d03f8cf-8d40-5475-8253-eb70c9fdece3
-- title:
--   Weierstrass Curve: over eq to Spec
-- statement:
--   The Weierstrass Curve construction uses the over eq to Spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L242-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L242-L242

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

theorem GlobalTheory.WeierstrassCurve.over_eq_toSpec : scheme W ↘ Spec (.of R) = toSpec W := by sorry
