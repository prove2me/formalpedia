-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_chartZ_preimage_coordOpen_one
-- name    : GlobalTheory.WeierstrassCurve.chartZ_preimage_coordOpen_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:11.689322+00:00
-- url     : https://prove2.me/theorems/9683c1c6-20c4-5e3e-9966-71ed535b2703
-- title:
--   Weierstrass Curve: chart Z preimage coord Open one
-- statement:
--   The Weierstrass Curve construction uses the chart Z preimage coord Open one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L841-L843
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L841-L843

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

theorem GlobalTheory.WeierstrassCurve.chartZ_preimage_coordOpen_one :
    chartZ W ⁻¹ᵁ coordOpen W 1 = PrimeSpectrum.basicOpen (affineY W) := by sorry
