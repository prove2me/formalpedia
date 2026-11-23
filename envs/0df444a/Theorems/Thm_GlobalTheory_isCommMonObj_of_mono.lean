-- Prove2me | Theorems.Thm_GlobalTheory_isCommMonObj_of_mono
-- name    : GlobalTheory.isCommMonObj_of_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:29.529796+00:00
-- url     : https://prove2.me/theorems/a148a912-2414-49af-a33d-a9b7e84efdf3
-- title:
--   Global Theory: is Comm Mon Obj of mono
-- statement:
--   The Global Theory construction uses the is Comm Mon Obj of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsGrpObjOfFlatClosed.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsGrpObjOfFlatClosed.lean#L60-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsGrpObjOfFlatClosed
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
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

theorem GlobalTheory.isCommMonObj_of_mono [BraidedCategory C] {H G : C} [MonObj H] [MonObj G] (j : H ⟶ G)
    [Mono j] [IsMonHom j] [IsCommMonObj G] : IsCommMonObj H := by sorry
