-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_of_represents
-- name    : GlobalTheory.WeierstrassCurve.ofAffinePoint_of_represents
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:37.531377+00:00
-- url     : https://prove2.me/theorems/1aa55043-619a-482b-be92-a5f73cfd97c6
-- title:
--   Weierstrass Curve: of Affine Point of represents
-- statement:
--   The Weierstrass Curve construction uses the of Affine Point of represents property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L373-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L373-L376

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

theorem GlobalTheory.WeierstrassCurve.ofAffinePoint_of_represents {P : Fin 3 → k} {p : (W.baseChange k).toAffine.Point}
    (h : AddLaw.Represents (W.baseChange k).toProjective P p) :
    ofAffinePoint W k p = ptOver W P (.of_nonsingular h.left) := by sorry
