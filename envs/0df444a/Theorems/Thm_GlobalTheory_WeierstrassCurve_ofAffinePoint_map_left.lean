-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_map_left
-- name    : GlobalTheory.WeierstrassCurve.ofAffinePoint_map_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:25:09.037377+00:00
-- url     : https://prove2.me/theorems/94e71687-1d7e-44c5-a392-d39185671f50
-- title:
--   Weierstrass Curve: of Affine Point map left
-- statement:
--   The Weierstrass Curve construction uses the of Affine Point map left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L395-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L395-L407

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
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
variable {k K}

theorem GlobalTheory.WeierstrassCurve.ofAffinePoint_map_left [DecidableEq k] [DecidableEq K] {S : Type*} [CommRing S]
    [Algebra R S] [Algebra S k] [IsScalarTower R S k] [Algebra S K] [IsScalarTower R S K]
    (f : k →ₐ[S] K) (p : (W.baseChange k).toAffine.Point) :
    (ofAffinePoint W K (WeierstrassCurve.Affine.Point.map (W' := W.toAffine) f p)).left =
      Spec.map (CommRingCat.ofHom (f : k →+* K)) ≫ (ofAffinePoint W k p).left := by sorry
