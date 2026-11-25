-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_isSumTriple_diagXYZ
-- name    : GlobalTheory.WeierstrassCurve.isSumTriple_diagXYZ
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:49:00.336869+00:00
-- url     : https://prove2.me/theorems/4acf81ff-0007-42f1-a6c5-fa1ff68d369e
-- title:
--   Weierstrass Curve: is Sum Triple diag XYZ
-- statement:
--   The Weierstrass Curve construction uses the is Sum Triple diag XYZ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L247-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L247-L249

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

theorem GlobalTheory.WeierstrassCurve.isSumTriple_diagXYZ (hP : V.toProjective.Equation P) (hQ : V.toProjective.Equation Q) :
    IsSumTriple V P Q (diagXYZ V.toProjective P Q) := by sorry
