-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_IsSumTriple_equation_of_isReduced
-- name    : GlobalTheory.WeierstrassCurve.IsSumTriple.equation_of_isReduced
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:14.537243+00:00
-- url     : https://prove2.me/theorems/c965575e-0f76-4def-afc0-d82fdc4b6ceb
-- title:
--   Is Sum Triple: equation of is Reduced
-- statement:
--   The Is Sum Triple construction uses the equation of is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L290-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L290-L300

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
open AddLaw
variable {A B : Type*} [CommRing A] [CommRing B]
variable {V : WeierstrassCurve A} {P Q T : Fin 3 → A}

theorem GlobalTheory.WeierstrassCurve.IsSumTriple.equation_of_isReduced {A : Type u} [CommRing A] [_root_.IsReduced A]
    {V : WeierstrassCurve A} [V.IsElliptic] {P Q T : Fin 3 → A} (h : IsSumTriple V P Q T)
    (hP : IsUnimodularSol V P) (hQ : IsUnimodularSol V Q) : V.toProjective.Equation T := by sorry
