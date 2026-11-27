-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_zsmul
-- name    : GlobalTheory.WeierstrassCurve.ofAffinePoint_zsmul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:35.836964+00:00
-- url     : https://prove2.me/theorems/8c4588a8-8f73-4407-ac97-59d77e48325f
-- title:
--   Weierstrass Curve: of Affine Point zsmul
-- statement:
--   The Weierstrass Curve construction uses the of Affine Point zsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsLiftAddOfIsReducedEq.lean#L395-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsLiftAddOfIsReducedEq.lean#L395-L397

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsLiftAddOfIsReducedEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
open AddLaw
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [W.IsElliptic]
variable (k : Type u) [Field k] [Algebra R k]
variable [DecidableEq k]

theorem GlobalTheory.WeierstrassCurve.ofAffinePoint_zsmul (n : ℤ) (p : (W.baseChange k).toAffine.Point) :
    ofAffinePoint W k (n • p) = ofAffinePoint W k p ^ n := by sorry
