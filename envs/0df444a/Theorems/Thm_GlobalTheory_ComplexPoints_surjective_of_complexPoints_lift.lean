-- Prove2me | Theorems.Thm_GlobalTheory_ComplexPoints_surjective_of_complexPoints_lift
-- name    : GlobalTheory.ComplexPoints.surjective_of_complexPoints_lift
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:25:35.348799+00:00
-- url     : https://prove2.me/theorems/3d6d09a5-3949-4d6c-b8c9-4475c27dea68
-- title:
--   Complex Points: surjective of complex Points lift
-- statement:
--   The Complex Points construction uses the surjective of complex Points lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L274-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L274-L278

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.ComplexPoints
variable {X Y : Scheme.{0}}

theorem GlobalTheory.ComplexPoints.surjective_of_complexPoints_lift {k : Type} [Field k] (σ : k →+* ℂ) {A B : Scheme.{0}}
    (a : A ⟶ Sp k) [LocallyOfFiniteType a] (ψ : B ⟶ A) (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Sp ℂ ⟶ A, x ≫ a = spMap σ → ∃ y : Sp ℂ ⟶ B, y ≫ ψ = x) : Surjective ψ := by sorry
