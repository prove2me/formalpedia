-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_symm_ptOver
-- name    : GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_ptOver
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:19.14401+00:00
-- url     : https://prove2.me/theorems/eaf104a9-c15c-5330-bd00-9bb5d0ad2d3e
-- title:
--   Weierstrass Curve: affine Point Equiv symm pt Over
-- statement:
--   The Weierstrass Curve construction uses the affine Point Equiv symm pt Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L454-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L454-L457

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
variable {k}

theorem GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_ptOver (P : Fin 3 → k) (h : IsUnimodularSol (W.baseChange k) P) :
    (affinePointEquiv W k).symm (ptOver W P h) =
      WeierstrassCurve.Projective.Point.toAffine (W.baseChange k).toProjective P := by sorry
