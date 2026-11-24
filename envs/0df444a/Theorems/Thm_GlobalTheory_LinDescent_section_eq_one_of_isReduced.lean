-- Prove2me | Theorems.Thm_GlobalTheory_LinDescent_section_eq_one_of_isReduced
-- name    : GlobalTheory.LinDescent.section_eq_one_of_isReduced
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:09:33.256297+00:00
-- url     : https://prove2.me/theorems/7a99fb2b-ca8c-4128-805c-071dd0a007d1
-- title:
--   Lin Descent: section eq one of is Reduced
-- statement:
--   The Lin Descent construction uses the section eq one of is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDescentOfIsReduced.lean#L651-L678
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDescentOfIsReduced.lean#L651-L678

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

theorem GlobalTheory.LinDescent.section_eq_one_of_isReduced {S : Scheme.{0}} [IsReduced S] {B : Over S} [GrpObj B]
    (y : 𝟙_ (Over S) ⟶ B)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), toUnit (Over.mk t) ≫ y = 1) :
    y = 1 := by sorry
