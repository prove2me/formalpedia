-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_ofProjectivePoint_comp_left
-- name    : GlobalTheory.WeierstrassCurve.ofProjectivePoint_comp_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:55:00.678884+00:00
-- url     : https://prove2.me/theorems/22437c0d-8fd8-4203-847b-f8847461a8af
-- title:
--   Weierstrass Curve: of Projective Point comp left
-- statement:
--   The Weierstrass Curve construction uses the of Projective Point comp left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L386-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L386-L391

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

theorem GlobalTheory.WeierstrassCurve.ofProjectivePoint_comp_left (f : k →ₐ[R] K) {P : Fin 3 → k}
    (h : (W.baseChange k).toProjective.NonsingularLift (Quotient.mk _ P))
    (h' : (W.baseChange K).toProjective.NonsingularLift (Quotient.mk _ (f ∘ P))) :
    (ofProjectivePoint W K ⟨h'⟩).left =
      Spec.map (CommRingCat.ofHom (f : k →+* K)) ≫ (ofProjectivePoint W k ⟨h⟩).left := by sorry
