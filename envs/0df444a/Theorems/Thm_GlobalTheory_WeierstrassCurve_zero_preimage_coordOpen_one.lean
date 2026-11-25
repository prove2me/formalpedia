-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_zero_preimage_coordOpen_one
-- name    : GlobalTheory.WeierstrassCurve.zero_preimage_coordOpen_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:00:41.638894+00:00
-- url     : https://prove2.me/theorems/ef991fd5-7fe1-488c-b577-b118e258d8b9
-- title:
--   Weierstrass Curve: zero preimage coord Open one
-- statement:
--   The Weierstrass Curve construction uses the zero preimage coord Open one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L376-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L376-L378

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

theorem GlobalTheory.WeierstrassCurve.zero_preimage_coordOpen_one : zero W ⁻¹ᵁ coordOpen W 1 = ⊤ := by sorry
