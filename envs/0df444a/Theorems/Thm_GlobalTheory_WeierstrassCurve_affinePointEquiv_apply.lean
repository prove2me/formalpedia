-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_apply
-- name    : GlobalTheory.WeierstrassCurve.affinePointEquiv_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:25:58.081616+00:00
-- url     : https://prove2.me/theorems/dc7565cc-6416-4678-9b01-a9a5d85667ba
-- title:
--   Weierstrass Curve: affine Point Equiv apply
-- statement:
--   The Weierstrass Curve construction uses the affine Point Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L433-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L433-L434

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
variable [(W.baseChange k).IsElliptic] [(W.baseChange K).IsElliptic]

theorem GlobalTheory.WeierstrassCurve.affinePointEquiv_apply (p : (W.baseChange k).toAffine.Point) :
    affinePointEquiv W k p = ofAffinePoint W k p := by sorry

attribute [defeq] GlobalTheory.WeierstrassCurve.affinePointEquiv_apply
