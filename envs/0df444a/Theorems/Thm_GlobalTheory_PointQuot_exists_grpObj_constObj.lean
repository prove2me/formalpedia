-- Prove2me | Theorems.Thm_GlobalTheory_PointQuot_exists_grpObj_constObj
-- name    : GlobalTheory.PointQuot.exists_grpObj_constObj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:49:11.664294+00:00
-- url     : https://prove2.me/theorems/c642528f-7e27-4de8-b233-5d6ee5721565
-- title:
--   Point Quot: exists grp Obj const Obj
-- statement:
--   The Point Quot construction uses the exists grp Obj const Obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientByFiniteGroupOfPoints.lean#L174-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientByFiniteGroupOfPoints.lean#L174-L193

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientByFiniteGroupOfPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.PointQuot
variable {S : Scheme.{0}}

theorem GlobalTheory.PointQuot.exists_grpObj_constObj {I : Type} {A : Over S} [GrpObj A] (x : I → (𝟙_ (Over S) ⟶ A))
    [Mono (constDesc x)] (C : Subgroup (𝟙_ (Over S) ⟶ A)) (hC : Set.range x = C) :
    ∃ _ : GrpObj (constObj S I), IsMonHom (constDesc x) := by sorry
