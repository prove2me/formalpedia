-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_exists_law_notMem
-- name    : GlobalTheory.WeierstrassCurve.exists_law_notMem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:54:05.035213+00:00
-- url     : https://prove2.me/theorems/82df0f00-d40e-46aa-a892-91aed105ba7f
-- title:
--   Weierstrass Curve: exists law not Mem
-- statement:
--   The Weierstrass Curve construction uses the exists law not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L276-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L276-L288

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

theorem GlobalTheory.WeierstrassCurve.exists_law_notMem [V.IsElliptic] (hP : IsUnimodularSol V P) (hQ : IsUnimodularSol V Q)
    (p : Ideal A) [p.IsPrime] :
    (∃ i, V.toProjective.addXYZ P Q i ∉ p) ∨ ∃ i, diagXYZ V.toProjective P Q i ∉ p := by sorry
