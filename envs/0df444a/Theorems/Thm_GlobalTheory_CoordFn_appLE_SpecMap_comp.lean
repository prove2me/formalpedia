-- Prove2me | Theorems.Thm_GlobalTheory_CoordFn_appLE_SpecMap_comp
-- name    : GlobalTheory.CoordFn.appLE_SpecMap_comp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:37:16.535047+00:00
-- url     : https://prove2.me/theorems/0ea12425-4735-528c-b699-99608031252e
-- title:
--   Coord Fn: app LE Spec Map comp
-- statement:
--   The Coord Fn construction uses the app LE Spec Map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsIsoAppLEOfOpensRange.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsIsoAppLEOfOpensRange.lean#L23-L31

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

theorem GlobalTheory.CoordFn.appLE_SpecMap_comp {Y : Scheme.{0}} {A B : CommRingCat.{0}} (f : Spec B ⟶ Y) (g : B ⟶ A)
    (U : Y.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (p : Spec A ⟶ Y) (hp : p = Spec.map g ≫ f)
    (h' : ⊤ ≤ p ⁻¹ᵁ U) :
    p.appLE U ⊤ h' ≫ (Scheme.ΓSpecIso A).hom = f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom ≫ g := by sorry
