-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_hom_schemeOver_eq_iff
-- name    : GlobalTheory.WeierstrassCurve.hom_schemeOver_eq_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:15.92883+00:00
-- url     : https://prove2.me/theorems/33d36eda-9aa0-532f-a4ef-717084d9ec2e
-- title:
--   Weierstrass Curve: hom scheme Over eq iff
-- statement:
--   The Weierstrass Curve construction uses the hom scheme Over eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L475-L480
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L475-L480

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

theorem GlobalTheory.WeierstrassCurve.hom_schemeOver_eq_iff {T : Over (Spec (.of R))} [IsReduced T.left]
    {f g : T ⟶ schemeOver W} :
    f = g ↔ ∀ (k : Type u) [Field k] [Algebra R k]
      (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ T), x ≫ f = x ≫ g := by sorry
