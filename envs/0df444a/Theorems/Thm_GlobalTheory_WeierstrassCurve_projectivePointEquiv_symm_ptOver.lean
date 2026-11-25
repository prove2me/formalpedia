-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_symm_ptOver
-- name    : GlobalTheory.WeierstrassCurve.projectivePointEquiv_symm_ptOver
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:24:20.54533+00:00
-- url     : https://prove2.me/theorems/ba6652cf-9fff-552c-ba6c-5440ae029b47
-- title:
--   Weierstrass Curve: projective Point Equiv symm pt Over
-- statement:
--   The Weierstrass Curve construction uses the projective Point Equiv symm pt Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L446-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L446-L450

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

theorem GlobalTheory.WeierstrassCurve.projectivePointEquiv_symm_ptOver (P : Fin 3 → k)
    (h : IsUnimodularSol (W.baseChange k) P) :
    (projectivePointEquiv W k).symm (ptOver W P h) =
      ⟨(WeierstrassCurve.Projective.nonsingularLift_iff P).mpr h.nonsingular⟩ := by sorry
