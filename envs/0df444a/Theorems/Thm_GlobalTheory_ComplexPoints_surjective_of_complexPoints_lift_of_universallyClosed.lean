-- Prove2me | Theorems.Thm_GlobalTheory_ComplexPoints_surjective_of_complexPoints_lift_of_universallyClosed
-- name    : GlobalTheory.ComplexPoints.surjective_of_complexPoints_lift_of_universallyClosed
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:36.652875+00:00
-- url     : https://prove2.me/theorems/88cbf352-0309-4c07-bead-8310c7eda3eb
-- title:
--   Complex Points: surjective of complex Points lift of universally Closed
-- statement:
--   The Complex Points construction uses the surjective of complex Points lift of universally Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L280-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L280-L286

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

theorem GlobalTheory.ComplexPoints.surjective_of_complexPoints_lift_of_universallyClosed {k : Type} [Field k] (σ : k →+* ℂ)
    {A B : Scheme.{0}} (a : A ⟶ Sp k) [LocallyOfFiniteType a] [IsSeparated a] (b : B ⟶ Sp k)
    [UniversallyClosed b] (ψ : B ⟶ A) (hw : ψ ≫ a = b)
    (h : ∀ x : Sp ℂ ⟶ A, x ≫ a = spMap σ → ∃ y : Sp ℂ ⟶ B, y ≫ ψ = x) : Surjective ψ := by sorry
