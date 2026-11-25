-- Prove2me | Theorems.Thm_GlobalTheory_isSemiAbelian_of_isAbelianScheme
-- name    : GlobalTheory.isSemiAbelian_of_isAbelianScheme
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:45:32.120175+00:00
-- url     : https://prove2.me/theorems/b027a18f-7da1-477b-a982-686385620d81
-- title:
--   Global Theory: is Semi Abelian of is Abelian Scheme
-- statement:
--   The Global Theory construction uses the is Semi Abelian of is Abelian Scheme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsAbelianSchemeAndExtendOfGenericHoms.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsAbelianSchemeAndExtendOfGenericHoms.lean#L44-L51

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

theorem GlobalTheory.isSemiAbelian_of_isAbelianScheme {S : Scheme.{0}} (A : Over S) [GrpObj A]
    (h : IsAbelianScheme A) : IsSemiAbelian A := by sorry
