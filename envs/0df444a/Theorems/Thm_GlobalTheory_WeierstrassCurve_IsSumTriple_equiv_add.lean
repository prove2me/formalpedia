-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_IsSumTriple_equiv_add
-- name    : GlobalTheory.WeierstrassCurve.IsSumTriple.equiv_add
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:47:16.669685+00:00
-- url     : https://prove2.me/theorems/4bd0fe8c-9179-5600-a95a-c580227ea8b4
-- title:
--   Is Sum Triple: equiv add
-- statement:
--   The Is Sum Triple construction uses the equiv add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L271-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L271-L274

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
open WeierstrassCurve.Projective

theorem GlobalTheory.WeierstrassCurve.IsSumTriple.equiv_add {k : Type*} [Field k] {V : WeierstrassCurve k} {P Q T : Fin 3 → k}
    (h : IsSumTriple V P Q T) (hP : V.toProjective.Nonsingular P)
    (hQ : V.toProjective.Nonsingular Q) (hT : T ≠ 0) : T ≈ V.toProjective.add P Q := by sorry
