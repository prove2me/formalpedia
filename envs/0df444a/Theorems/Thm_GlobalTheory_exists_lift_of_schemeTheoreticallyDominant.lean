-- Prove2me | Theorems.Thm_GlobalTheory_exists_lift_of_schemeTheoreticallyDominant
-- name    : GlobalTheory.exists_lift_of_schemeTheoreticallyDominant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:43.790806+00:00
-- url     : https://prove2.me/theorems/da5543df-2de2-41c2-9d75-1a5bcd0fd3dd
-- title:
--   Global Theory: exists lift of scheme Theoretically Dominant
-- statement:
--   The Global Theory construction uses the exists lift of scheme Theoretically Dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLiftOfSchemeTheoreticallyDominant.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLiftOfSchemeTheoreticallyDominant.lean#L10-L16

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
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

theorem GlobalTheory.exists_lift_of_schemeTheoreticallyDominant {W Y X Z : Scheme.{0}} (φ : W ⟶ Y)
    [IsSchemeTheoreticallyDominant φ] (i : Z ⟶ X) [IsClosedImmersion i] (a : Y ⟶ X) (c : W ⟶ Z)
    (h : c ≫ i = φ ≫ a) : ∃ b : Y ⟶ Z, b ≫ i = a := by sorry
