-- Prove2me | Theorems.Thm_GlobalTheory_hom_ext_of_localRing_points
-- name    : GlobalTheory.hom_ext_of_localRing_points
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:51.529645+00:00
-- url     : https://prove2.me/theorems/9922c892-e942-5785-9418-164addcab78c
-- title:
--   Global Theory: hom ext of local Ring points
-- statement:
--   The Global Theory construction uses the hom ext of local Ring points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HomExtOfLocalRingPoints.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HomExtOfLocalRingPoints.lean#L10-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HomExtOfLocalRingPoints
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
open GlobalTheory

theorem GlobalTheory.hom_ext_of_localRing_points :
    ∀ (X Y : Scheme.{0}) (f g : X ⟶ Y),
      (∀ (A : Type) [CommRing A] [IsLocalRing A] (t : Sp A ⟶ X), t ≫ f = t ≫ g) → f = g := by sorry
