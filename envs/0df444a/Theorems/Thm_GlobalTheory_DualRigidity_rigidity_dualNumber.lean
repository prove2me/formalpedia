-- Prove2me | Theorems.Thm_GlobalTheory_DualRigidity_rigidity_dualNumber
-- name    : GlobalTheory.DualRigidity.rigidity_dualNumber
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:35.495525+00:00
-- url     : https://prove2.me/theorems/57d51110-5581-4daa-a175-fadd81ef1ac8
-- title:
--   Dual Rigidity: rigidity dual Number
-- statement:
--   The Dual Rigidity construction uses the rigidity dual Number property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SubsingletonSpDualNumber.lean#L43-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SubsingletonSpDualNumber.lean#L43-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqCompSectionOfSurjectiveAppTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SubsingletonSpDualNumber
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
open GlobalTheory GlobalTheory.DualRigidity

theorem GlobalTheory.DualRigidity.rigidity_dualNumber : Out.Laws → Out.Laws2 → ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (A' G' : Over (Sp (DualNumber ℂ))) [GrpObj A'] [GrpObj G'] (j : A₀.left ⟶ A'.left) (a b : A' ⟶ G'), IsAbelianScheme A' → IsPullback j A₀.hom A'.hom (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → j ≫ a.left = j ≫ b.left → η[A'] ≫ a = η[A'] ≫ b → a = b := by sorry
