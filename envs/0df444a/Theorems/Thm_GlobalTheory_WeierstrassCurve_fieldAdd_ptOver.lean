-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_fieldAdd_ptOver
-- name    : GlobalTheory.WeierstrassCurve.fieldAdd_ptOver
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:47:24.525082+00:00
-- url     : https://prove2.me/theorems/cbb37321-9e1f-5300-b5f1-5f5af590a65b
-- title:
--   Weierstrass Curve: field Add pt Over
-- statement:
--   The Weierstrass Curve construction uses the field Add pt Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L312-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L312-L321

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
variable [W.IsElliptic]

theorem GlobalTheory.WeierstrassCurve.fieldAdd_ptOver {k : Type u} [Field k] [Algebra R k] {P Q T : Fin 3 → k}
    (hP : IsUnimodularSol (W.baseChange k) P) (hQ : IsUnimodularSol (W.baseChange k) Q)
    (hT : IsUnimodularSol (W.baseChange k) T) (h : IsSumTriple (W.baseChange k) P Q T) :
    fieldAdd W k (ptOver W P hP) (ptOver W Q hQ) = ptOver W T hT := by sorry
