-- Prove2me | Theorems.Thm_GlobalTheory_ComplexPoints_closed_eq_univ_of_geomPoints
-- name    : GlobalTheory.ComplexPoints.closed_eq_univ_of_geomPoints
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:12.476591+00:00
-- url     : https://prove2.me/theorems/d130fc43-0498-416a-884a-3bdd1da1facb
-- title:
--   Complex Points: closed eq univ of geom Points
-- statement:
--   The Complex Points construction uses the closed eq univ of geom Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L69-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L69-L76

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

theorem GlobalTheory.ComplexPoints.closed_eq_univ_of_geomPoints {X S : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p]
    (t : Spec (.of K) ⟶ S) [Surjective t] {Z : Set X} (hZ : IsClosed Z)
    (h : ∀ x : Spec (.of K) ⟶ X, x ≫ p = t → ∃ a, x a ∈ Z) : Z = Set.univ := by sorry
