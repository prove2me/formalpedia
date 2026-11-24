-- Prove2me | Theorems.Thm_GlobalTheory_T_endo_constant_family_dualNumbers_eq_baseChange
-- name    : GlobalTheory.T.endo_constant_family_dualNumbers_eq_baseChange
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:33:15.439142+00:00
-- url     : https://prove2.me/theorems/379a9ca9-3997-45e6-8043-bee5461efcb0
-- title:
--   T: endo constant family dual Numbers eq base Change
-- statement:
--   The T construction uses the endo constant family dual Numbers eq base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EndoConstantFamilyDualNumbersEqBaseChangeStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EndoConstantFamilyDualNumbersEqBaseChangeStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EndoConstantFamilyDualNumbersEqBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EndoConstantFamilyDualNumbersEqBaseChangeStatement
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

theorem GlobalTheory.T.endo_constant_family_dualNumbers_eq_baseChange : Out.Laws → Out.Laws2 → ∀ (P₀ : Out.PolAV (Sp ℂ)), ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (f' : A' ⟶ A') (f₀ : P₀.A ⟶ P₀.A), IsAbelianScheme A' → IsMonHom f' → IsMonHom f₀ → j ≫ f'.left = f₀.left ≫ j → f'.left ≫ ρ = ρ ≫ f₀.left := by sorry
