-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_comp_ptOver_eq_fieldAdd
-- name    : GlobalTheory.WeierstrassCurve.comp_ptOver_eq_fieldAdd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:47:58.711027+00:00
-- url     : https://prove2.me/theorems/0e459eac-4945-471d-a797-392f25ceaca4
-- title:
--   Weierstrass Curve: comp pt Over eq field Add
-- statement:
--   The Weierstrass Curve construction uses the comp pt Over eq field Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L323-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L323-L330

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

theorem GlobalTheory.WeierstrassCurve.comp_ptOver_eq_fieldAdd {A : Type u} [CommRing A] [Algebra R A] {P Q T : Fin 3 → A}
    (hP : IsUnimodularSol (W.baseChange A) P) (hQ : IsUnimodularSol (W.baseChange A) Q)
    (hT : IsUnimodularSol (W.baseChange A) T) (h : IsSumTriple (W.baseChange A) P Q T)
    (k : Type u) [Field k] [Algebra R k] (x : specOver R k ⟶ specOver R A) :
    x ≫ ptOver W T hT = fieldAdd W k (x ≫ ptOver W P hP) (x ≫ ptOver W Q hQ) := by sorry
