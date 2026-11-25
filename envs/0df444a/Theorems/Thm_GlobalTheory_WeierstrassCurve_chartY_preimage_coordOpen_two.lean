-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_chartY_preimage_coordOpen_two
-- name    : GlobalTheory.WeierstrassCurve.chartY_preimage_coordOpen_two
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:13:49.997445+00:00
-- url     : https://prove2.me/theorems/6cfa5d5c-655d-4be9-8527-2ea422b3d981
-- title:
--   Weierstrass Curve: chart Y preimage coord Open two
-- statement:
--   The Weierstrass Curve construction uses the chart Y preimage coord Open two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L837-L839
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L837-L839

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

theorem GlobalTheory.WeierstrassCurve.chartY_preimage_coordOpen_two :
    chartY W ⁻¹ᵁ coordOpen W 2 = PrimeSpectrum.basicOpen (originW W) := by sorry
