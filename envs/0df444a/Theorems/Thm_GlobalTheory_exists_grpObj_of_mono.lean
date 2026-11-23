-- Prove2me | Theorems.Thm_GlobalTheory_exists_grpObj_of_mono
-- name    : GlobalTheory.exists_grpObj_of_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:19.456136+00:00
-- url     : https://prove2.me/theorems/47f67f3c-c4a4-4e43-a048-9623ad1f301d
-- title:
--   Global Theory: exists grp Obj of mono
-- statement:
--   The Global Theory construction uses the exists grp Obj of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsGrpObjOfFlatClosed.lean#L16-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsGrpObjOfFlatClosed.lean#L16-L51

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

theorem GlobalTheory.exists_grpObj_of_mono {H G : C} [GrpObj G] (j : H ⟶ G) [Mono j]
    (o : 𝟙_ C ⟶ H) (m : H ⊗ H ⟶ H) (n : H ⟶ H) (ho : o ≫ j = η[G])
    (hm : m ≫ j = (j ⊗ₘ j) ≫ μ[G]) (hn : n ≫ j = j ≫ GrpObj.inv) :
    ∃ _ : GrpObj H, IsMonHom j := by sorry
