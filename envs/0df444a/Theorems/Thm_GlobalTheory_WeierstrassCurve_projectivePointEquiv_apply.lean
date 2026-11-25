-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_apply
-- name    : GlobalTheory.WeierstrassCurve.projectivePointEquiv_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:25:59.919723+00:00
-- url     : https://prove2.me/theorems/7529c085-8cd8-429f-8876-1142766818b6
-- title:
--   Weierstrass Curve: projective Point Equiv apply
-- statement:
--   The Weierstrass Curve construction uses the projective Point Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L430-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L430-L431

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

theorem GlobalTheory.WeierstrassCurve.projectivePointEquiv_apply (p : (W.baseChange k).toProjective.Point) :
    projectivePointEquiv W k p = ofProjectivePoint W k p := by sorry

attribute [defeq] GlobalTheory.WeierstrassCurve.projectivePointEquiv_apply
