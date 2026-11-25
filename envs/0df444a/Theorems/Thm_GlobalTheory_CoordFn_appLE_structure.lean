-- Prove2me | Theorems.Thm_GlobalTheory_CoordFn_appLE_structure
-- name    : GlobalTheory.CoordFn.appLE_structure
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:36:59.35273+00:00
-- url     : https://prove2.me/theorems/80758f4c-61c6-5d6f-b25d-f6390235a599
-- title:
--   Coord Fn: app LE structure
-- statement:
--   The Coord Fn construction uses the app LE structure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsIsoAppLEOfOpensRange.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsIsoAppLEOfOpensRange.lean#L33-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsIsoAppLEOfOpensRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
open GlobalTheory GlobalTheory.CoordFn

theorem GlobalTheory.CoordFn.appLE_structure {Y : Scheme.{0}} {A B : CommRingCat.{0}} (f : Spec B ⟶ Y) (g : A ⟶ B)
    (U : Y.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (t : Y ⟶ Spec A) (ht : f ≫ t = Spec.map g) :
    (Scheme.ΓSpecIso A).inv ≫ t.appLE ⊤ U le_top ≫ f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom = g := by sorry
