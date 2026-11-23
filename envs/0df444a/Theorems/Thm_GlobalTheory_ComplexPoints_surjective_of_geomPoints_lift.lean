-- Prove2me | Theorems.Thm_GlobalTheory_ComplexPoints_surjective_of_geomPoints_lift
-- name    : GlobalTheory.ComplexPoints.surjective_of_geomPoints_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:18.91304+00:00
-- url     : https://prove2.me/theorems/f3a539f4-b9a0-4131-b9a6-e469050aa8c5
-- title:
--   Complex Points: surjective of geom Points lift
-- statement:
--   The Complex Points construction uses the surjective of geom Points lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L82-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L82-L103

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
variable {K : Type u} [Field K] [IsAlgClosed K]
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {K : Type u} [Field K] [IsAlgClosed K]

theorem GlobalTheory.ComplexPoints.surjective_of_geomPoints_lift {A B S : Scheme.{u}} (p : A ⟶ S)
    [LocallyOfFiniteType p]
    (t : Spec (.of K) ⟶ S) [Surjective t] (ψ : B ⟶ A) (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Spec (.of K) ⟶ A, x ≫ p = t → ∃ y : Spec (.of K) ⟶ B, y ≫ ψ = x) :
    Surjective ψ := by sorry
