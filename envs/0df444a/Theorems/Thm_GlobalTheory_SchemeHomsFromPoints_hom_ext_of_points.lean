-- Prove2me | Theorems.Thm_GlobalTheory_SchemeHomsFromPoints_hom_ext_of_points
-- name    : GlobalTheory.SchemeHomsFromPoints.hom_ext_of_points
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:33:11.754328+00:00
-- url     : https://prove2.me/theorems/53dc26c3-57c2-43b4-8475-82bf3e235e4a
-- title:
--   Scheme Homs From Points: hom ext of points
-- statement:
--   The Scheme Homs From Points construction uses the hom ext of points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/DenseClosedPoints.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/DenseClosedPoints.lean#L15-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp valAt valAt')
open GlobalTheory GlobalTheory.SchemeHomsFromPoints

theorem GlobalTheory.SchemeHomsFromPoints.hom_ext_of_points {X Y : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    [Y.IsSeparated] (f g : X ⟶ Y) (H : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → x ≫ f = x ≫ g) : f = g := by sorry
