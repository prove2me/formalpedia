-- Prove2me | Theorems.Thm_GlobalTheory_exists_grpObj_of_flat_closed
-- name    : GlobalTheory.exists_grpObj_of_flat_closed
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:15.683145+00:00
-- url     : https://prove2.me/theorems/0dad7b84-1051-4cd3-95ee-572127d214cf
-- title:
--   Global Theory: exists grp Obj of flat closed
-- statement:
--   The Global Theory construction uses the exists grp Obj of flat closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsGrpObjOfFlatClosed.lean#L68-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsGrpObjOfFlatClosed.lean#L68-L96

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

theorem GlobalTheory.exists_grpObj_of_flat_closed {S S' : Scheme.{0}} (f : S' ⟶ S)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] (P Ga : Over S) [GrpObj P] (io : Ga ⟶ P)
    (Z : Over S') [GrpObj Z] (i : Z ⟶ (Over.pullback f).obj P) (e : (Over.pullback f).obj Ga ≅ Z)
    [IsClosedImmersion io.left] [Flat Ga.hom] [hi : IsMonHom i]
    (h : e.hom ≫ i = (Over.pullback f).map io) :
    ∃ _ : GrpObj Ga, IsMonHom io ∧ IsMonHom e.hom ∧ (IsCommMonObj P → IsCommMonObj Ga) := by sorry
