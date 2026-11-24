-- Prove2me | Theorems.Thm_GlobalTheory_PointQuot_exists_grpObj_of_mono
-- name    : GlobalTheory.PointQuot.exists_grpObj_of_mono
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:50:05.365478+00:00
-- url     : https://prove2.me/theorems/e0073895-644d-4b12-993a-3dbf0a9a789b
-- title:
--   Point Quot: exists grp Obj of mono
-- statement:
--   The Point Quot construction uses the exists grp Obj of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientByFiniteGroupOfPoints.lean#L19-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientByFiniteGroupOfPoints.lean#L19-L47

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

theorem GlobalTheory.PointQuot.exists_grpObj_of_mono {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] {H A : 𝒞}
    [GrpObj A] (i : H ⟶ A) [Mono i] (e : 𝟙_ 𝒞 ⟶ H) (m : H ⊗ H ⟶ H) (n : H ⟶ H)
    (he : e ≫ i = 1) (hm : m ≫ i = (fst H H ≫ i) * (snd H H ≫ i)) (hn : n ≫ i = i⁻¹) :
    ∃ _ : GrpObj H, IsMonHom i := by sorry
