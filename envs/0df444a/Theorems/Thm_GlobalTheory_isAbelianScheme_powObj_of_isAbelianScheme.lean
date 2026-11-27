-- Prove2me | Theorems.Thm_GlobalTheory_isAbelianScheme_powObj_of_isAbelianScheme
-- name    : GlobalTheory.isAbelianScheme_powObj_of_isAbelianScheme
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:49:05.57794+00:00
-- url     : https://prove2.me/theorems/acc26b9a-2536-4112-90a1-389dde3d58be
-- title:
--   Global Theory: is Abelian Scheme pow Obj of is Abelian Scheme
-- statement:
--   The Global Theory construction uses the is Abelian Scheme pow Obj of is Abelian Scheme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsAbelianSchemeAndExtendOfGenericHoms.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsAbelianSchemeAndExtendOfGenericHoms.lean#L53-L56

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

theorem GlobalTheory.isAbelianScheme_powObj_of_isAbelianScheme {S : Scheme.{0}} (A : Over S) [GrpObj A]
    (h : IsAbelianScheme A) : ∀ n, IsAbelianScheme (Out.powObj A n)
  := by sorry
