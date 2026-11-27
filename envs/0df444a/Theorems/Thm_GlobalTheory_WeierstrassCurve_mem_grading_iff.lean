-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_mem_grading_iff
-- name    : GlobalTheory.WeierstrassCurve.mem_grading_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:27.561858+00:00
-- url     : https://prove2.me/theorems/3d8cdb0d-c004-5d57-bcda-abff948c381b
-- title:
--   Weierstrass Curve: mem grading iff
-- statement:
--   The Weierstrass Curve construction uses the mem grading iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L135-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L135-L137

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

theorem GlobalTheory.WeierstrassCurve.mem_grading_iff {n : ℕ} {a : HomRing W} :
    a ∈ grading W n ↔ ∃ p : MvPolynomial (Fin 3) R, p.IsHomogeneous n ∧
      Ideal.Quotient.mk _ p = a := by sorry
