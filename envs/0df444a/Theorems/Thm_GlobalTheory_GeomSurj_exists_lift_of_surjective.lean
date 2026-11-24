-- Prove2me | Theorems.Thm_GlobalTheory_GeomSurj_exists_lift_of_surjective
-- name    : GlobalTheory.GeomSurj.exists_lift_of_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:14.726226+00:00
-- url     : https://prove2.me/theorems/d3e608ea-28b6-4fde-83c1-720057bdee6a
-- title:
--   Geom Surj: exists lift of surjective
-- statement:
--   The Geom Surj construction uses the exists lift of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ProdSurjectiveGeometricPoints.lean#L40-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ProdSurjectiveGeometricPoints.lean#L40-L77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ProdSurjectiveGeometricPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.GeomSurj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open scoped CategoryTheory.Obj

theorem GlobalTheory.GeomSurj.exists_lift_of_surjective {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P A : Scheme.{0}}
    (ψ : P ⟶ A) [LocallyOfFiniteType ψ] [Surjective ψ] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω ⟶ A) :
    ∃ p : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω ⟶ P, x = p ≫ ψ := by sorry
