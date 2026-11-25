-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_some
-- name    : GlobalTheory.WeierstrassCurve.ofAffinePoint_some
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:24:08.31087+00:00
-- url     : https://prove2.me/theorems/4f1f4f81-e022-5cb8-9724-32682209fdd8
-- title:
--   Weierstrass Curve: of Affine Point some
-- statement:
--   The Weierstrass Curve construction uses the of Affine Point some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L353-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L353-L354

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

theorem GlobalTheory.WeierstrassCurve.ofAffinePoint_some {a b : k} (h : (W.baseChange k).toAffine.Nonsingular a b) :
    ofAffinePoint W k (.some a b h) = ptOver W ![a, b, 1] (isUnimodularSol_some h.left) := by sorry

attribute [defeq] GlobalTheory.WeierstrassCurve.ofAffinePoint_some
