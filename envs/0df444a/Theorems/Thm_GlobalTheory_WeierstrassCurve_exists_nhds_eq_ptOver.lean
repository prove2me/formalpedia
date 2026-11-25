-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_exists_nhds_eq_ptOver
-- name    : GlobalTheory.WeierstrassCurve.exists_nhds_eq_ptOver
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:11.188283+00:00
-- url     : https://prove2.me/theorems/1f355192-2ea0-5e50-a4f0-a9e04b54951a
-- title:
--   Weierstrass Curve: exists nhds eq pt Over
-- statement:
--   The Weierstrass Curve construction uses the exists nhds eq pt Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L334-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L334-L350

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
omit [W.IsElliptic]

theorem GlobalTheory.WeierstrassCurve.exists_nhds_eq_ptOver {T : Over (Spec (.of R))} (p q : T ⟶ schemeOver W) (t : T.left) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (j : specOver R A ⟶ T) (P Q : Fin 3 → A)
      (hP : IsUnimodularSol (W.baseChange A) P) (hQ : IsUnimodularSol (W.baseChange A) Q),
      IsOpenImmersion j.left ∧ t ∈ Set.range j.left ∧ j ≫ p = ptOver W P hP ∧
        j ≫ q = ptOver W Q hQ := by sorry
