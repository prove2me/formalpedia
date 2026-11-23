-- Prove2me | Theorems.Thm_GlobalTheory_ComplexPoints_over_hom_ext_of_complexPoints
-- name    : GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:12:20.370967+00:00
-- url     : https://prove2.me/theorems/da3bb09e-0f87-4421-9b79-3bb67c3bfaa3
-- title:
--   Complex Points: over hom ext of complex Points
-- statement:
--   The Complex Points construction uses the over hom ext of complex Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L240-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L240-L247

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
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {X Y : Scheme.{0}}

theorem GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints {A B : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)} [LocallyOfFiniteType A.hom]
    [IsReduced A.left] [IsSeparated B.hom] {f g : A ⟶ B}
    (h : ∀ x : 𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) ⟶ A, x ≫ f = x ≫ g) : f = g := by sorry
