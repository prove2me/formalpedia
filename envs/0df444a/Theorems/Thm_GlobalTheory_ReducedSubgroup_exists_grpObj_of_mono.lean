-- Prove2me | Theorems.Thm_GlobalTheory_ReducedSubgroup_exists_grpObj_of_mono
-- name    : GlobalTheory.ReducedSubgroup.exists_grpObj_of_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:16.899103+00:00
-- url     : https://prove2.me/theorems/b020fa32-c347-4fab-886a-c2d2d326f01c
-- title:
--   Reduced Subgroup: exists grp Obj of mono
-- statement:
--   The Reduced Subgroup construction uses the exists grp Obj of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GeometricallyReducedOfPerfectField.lean#L15-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GeometricallyReducedOfPerfectField.lean#L15-L48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
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
open GlobalTheory GlobalTheory.ReducedSubgroup
variable {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞]

theorem GlobalTheory.ReducedSubgroup.exists_grpObj_of_mono {N B : 𝒞} [GrpObj B] (ν : N ⟶ B) [Mono ν] (e : 𝟙_ 𝒞 ⟶ N)
    (m : N ⊗ N ⟶ N) (i : N ⟶ N) (he : e ≫ ν = η[B]) (hm : m ≫ ν = (ν ⊗ₘ ν) ≫ μ[B])
    (hi : i ≫ ν = ν ≫ GrpObj.inv) : ∃ _ : GrpObj N, IsMonHom ν := by sorry
