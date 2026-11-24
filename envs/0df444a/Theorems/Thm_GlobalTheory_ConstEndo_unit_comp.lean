-- Prove2me | Theorems.Thm_GlobalTheory_ConstEndo_unit_comp
-- name    : GlobalTheory.ConstEndo.unit_comp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:26:15.777827+00:00
-- url     : https://prove2.me/theorems/d533e5b1-3d15-405f-a19b-275587a5ce69
-- title:
--   Const Endo: unit comp
-- statement:
--   The Const Endo construction uses the unit comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EndoConstantFamilyDualNumbersEqBaseChange.lean#L17-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EndoConstantFamilyDualNumbersEqBaseChange.lean#L17-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SubsingletonSpDualNumber
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EndoConstantFamilyDualNumbersEqBaseChange
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.ConstEndo

theorem GlobalTheory.ConstEndo.unit_comp {S S₀ : Scheme.{0}} {f : S ⟶ S₀} {X : Over S} {X₀ : Over S₀} [GrpObj X] [GrpObj X₀]
    {φ : X.left ⟶ X₀.left} (h : IsGrpPullback X X₀ f φ) :
    (η[X]).left ≫ φ = f ≫ (η[X₀]).left := by sorry
