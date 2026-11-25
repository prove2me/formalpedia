-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_toUnit_zeroUnit
-- name    : GlobalTheory.WeierstrassCurve.toUnit_zeroUnit
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:51:12.493377+00:00
-- url     : https://prove2.me/theorems/dfd00b6a-26ba-46c1-9f87-acf7c8b677f5
-- title:
--   Weierstrass Curve: to Unit zero Unit
-- statement:
--   The Weierstrass Curve construction uses the to Unit zero Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L224-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L224-L225

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable {A : Type*} [CommRing A]

theorem GlobalTheory.WeierstrassCurve.toUnit_zeroUnit (A : Type u) [CommRing A] [Algebra R A] :
    toUnit (specOver R A) ≫ zeroUnit W = zeroOver W A := by sorry
