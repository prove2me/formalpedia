-- Prove2me | Theorems.Thm_GlobalTheory_exists_lift_of_isReduced_of_range_subset
-- name    : GlobalTheory.exists_lift_of_isReduced_of_range_subset
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:29.602963+00:00
-- url     : https://prove2.me/theorems/03668438-6527-4870-b3cc-70e5ec72c3f2
-- title:
--   Global Theory: exists lift of is Reduced of range subset
-- statement:
--   The Global Theory construction uses the exists lift of is Reduced of range subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLiftOfIsReducedOfRangeSubset.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLiftOfIsReducedOfRangeSubset.lean#L12-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedTorusExtensionOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfIsReducedOfRangeSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.exists_lift_of_isReduced_of_range_subset {Y X Z : Scheme.{0}} [IsReduced Y] (i : Z ⟶ X)
    [IsClosedImmersion i] (a : Y ⟶ X) (h : Set.range a ⊆ Set.range i) :
    ∃ b : Y ⟶ Z, b ≫ i = a := by sorry
