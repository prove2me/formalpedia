-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_isAffineOpen_coordOpen
-- name    : GlobalTheory.WeierstrassCurve.isAffineOpen_coordOpen
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:00:01.226635+00:00
-- url     : https://prove2.me/theorems/99baafb3-f682-5bc1-83eb-f6b1ef63cce6
-- title:
--   Weierstrass Curve: is Affine Open coord Open
-- statement:
--   The Weierstrass Curve construction uses the is Affine Open coord Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L493-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L493-L494

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
variable (i : Fin 3)
variable {A : Type u} [CommRing A]
variable (ρ : R →+* A) (P : Fin 3 → A)

theorem GlobalTheory.WeierstrassCurve.isAffineOpen_coordOpen : IsAffineOpen (coordOpen W i) := by sorry
