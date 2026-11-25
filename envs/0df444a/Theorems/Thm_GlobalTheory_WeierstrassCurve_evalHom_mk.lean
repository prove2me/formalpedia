-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_evalHom_mk
-- name    : GlobalTheory.WeierstrassCurve.evalHom_mk
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:12:56.14092+00:00
-- url     : https://prove2.me/theorems/799ad3dd-23dd-4707-86a0-9e896f8a2b61
-- title:
--   Weierstrass Curve: eval Hom mk
-- statement:
--   The Weierstrass Curve construction uses the eval Hom mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L192-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L192-L193

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal Limits
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable {A B : Type*} [CommRing A] [CommRing B]
variable (ρ : R →+* A) (P : Fin 3 → A) (h : (W.map ρ).toProjective.Equation P)

theorem GlobalTheory.WeierstrassCurve.evalHom_mk (p : MvPolynomial (Fin 3) R) :
    evalHom W ρ P h (Ideal.Quotient.mk _ p) = MvPolynomial.eval₂ ρ P p := by sorry
