-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_mul_left_mapHom
-- name    : GlobalTheory.WeierstrassCurve.mul_left_mapHom
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:05:04.509126+00:00
-- url     : https://prove2.me/theorems/89c6d93c-165f-40cd-8b89-5be11a19936e
-- title:
--   Weierstrass Curve: mul left map Hom
-- statement:
--   The Weierstrass Curve construction uses the mul left map Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsLiftAddOfIsReducedEq.lean#L232-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsLiftAddOfIsReducedEq.lean#L232-L256

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
variable {R' : Type u} [CommRing R'] {W' : WeierstrassCurve R'} [W'.IsElliptic] (f : R →+* R')
  (h : W.map f = W')

theorem GlobalTheory.WeierstrassCurve.mul_left_mapHom {T' : Over (Spec (.of R'))} {T : Over (Spec (.of R))}
    (t : T'.left ⟶ T.left) {x' y' : T' ⟶ schemeOver W'} {x y : T ⟶ schemeOver W}
    (hx : x'.left ≫ mapHom W f h = t ≫ x.left) (hy : y'.left ≫ mapHom W f h = t ≫ y.left) :
    (x' * y').left ≫ mapHom W f h = t ≫ (x * y).left := by sorry
