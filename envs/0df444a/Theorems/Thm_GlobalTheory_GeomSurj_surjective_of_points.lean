-- Prove2me | Theorems.Thm_GlobalTheory_GeomSurj_surjective_of_points
-- name    : GlobalTheory.GeomSurj.surjective_of_points
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:18.201802+00:00
-- url     : https://prove2.me/theorems/430993ff-d493-4f8f-b62f-9bab8d8e94e2
-- title:
--   Geom Surj: surjective of points
-- statement:
--   The Geom Surj construction uses the surjective of points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ProdSurjectiveGeometricPoints.lean#L11-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ProdSurjectiveGeometricPoints.lean#L11-L35

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

theorem GlobalTheory.GeomSurj.surjective_of_points {k K : Type} [Field k] [Field K] [IsAlgClosed K] (σ : k →+* K)
    {P A : Scheme.{0}} (a : A ⟶ Sp k) [LocallyOfFiniteType a] (ψ : P ⟶ A)
    (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Sp K ⟶ A, x ≫ a = spMap σ → ∃ p : Sp K ⟶ P, x = p ≫ ψ) : Surjective ψ := by sorry
