-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffineLift
-- name    : GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:29:50.946854+00:00
-- url     : https://prove2.me/theorems/cfa0676b-980a-416f-9c82-f83a8a0ccde2
-- title:
--   Weierstrass Curve: of Affine Point to Affine Lift
-- statement:
--   The Weierstrass Curve construction uses the of Affine Point to Affine Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L358-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L358-L362

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
variable {k}

theorem GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift (p : (W.baseChange k).toProjective.Point) :
    ofAffinePoint W k p.toAffineLift = ofProjectivePoint W k p := by sorry
