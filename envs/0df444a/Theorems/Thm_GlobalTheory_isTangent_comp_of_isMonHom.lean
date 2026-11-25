-- Prove2me | Theorems.Thm_GlobalTheory_isTangent_comp_of_isMonHom
-- name    : GlobalTheory.isTangent_comp_of_isMonHom
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:56:15.997995+00:00
-- url     : https://prove2.me/theorems/06f9f6a1-8d75-4f4d-887a-e919ca854012
-- title:
--   Global Theory: is Tangent comp of is Mon Hom
-- statement:
--   The Global Theory construction uses the is Tangent comp of is Mon Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsAbelianSchemeAndExtendOfGenericHoms.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsAbelianSchemeAndExtendOfGenericHoms.lean#L65-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeOfGenericallySurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory

theorem GlobalTheory.isTangent_comp_of_isMonHom {R : Type} [CommRing R] {B G : Over (Sp R)} [GrpObj B] [GrpObj G]
    (Φ : B ⟶ G) [IsMonHom Φ] (v : epsR R ⟶ B) (hv : IsTangent v) : IsTangent (v ≫ Φ) := by sorry
