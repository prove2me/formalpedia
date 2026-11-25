-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_symm_of_left_eq
-- name    : GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_of_left_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:08.624129+00:00
-- url     : https://prove2.me/theorems/28e77218-ef4c-53b6-bf06-1a6ff4495508
-- title:
--   Weierstrass Curve: affine Point Equiv symm of left eq
-- statement:
--   The Weierstrass Curve construction uses the affine Point Equiv symm of left eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L461-L471
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L461-L471

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (k K : Type u) [Field k] [Field K] [Algebra R k] [Algebra R K]
variable [(W.baseChange k).IsElliptic] [(W.baseChange K).IsElliptic]
variable {k K}

theorem GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_of_left_eq [DecidableEq k] [DecidableEq K] {S : Type*} [CommRing S]
    [Algebra R S] [Algebra S k] [IsScalarTower R S k] [Algebra S K] [IsScalarTower R S K]
    (f : k →ₐ[S] K)
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W)
    (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ schemeOver W)
    (h : y.left = Spec.map (CommRingCat.ofHom (f : k →+* K)) ≫ x.left) :
    (affinePointEquiv W K).symm y =
      WeierstrassCurve.Affine.Point.map (W' := W.toAffine) f ((affinePointEquiv W k).symm x) := by sorry
