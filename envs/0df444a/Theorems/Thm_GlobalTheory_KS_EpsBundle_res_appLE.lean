-- Prove2me | Theorems.Thm_GlobalTheory_KS_EpsBundle_res_appLE
-- name    : GlobalTheory.KS.EpsBundle.res_appLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:44.014804+00:00
-- url     : https://prove2.me/theorems/9d51c0f1-f9a9-407f-9fb2-4375b73c7f24
-- title:
--   Eps Bundle: res app LE
-- statement:
--   The Eps Bundle construction uses the res app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TrivialIffCoboundary.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TrivialIffCoboundary.lean#L20-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TrivialIffCoboundary
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
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EpsBundle

theorem GlobalTheory.KS.EpsBundle.res_appLE {Y Y' : Scheme.{0}} (ρ : Y' ⟶ Y) {O O' : Y.Opens} {W W' : Y'.Opens}
    (hW : W' ≤ W) (hO : O' ≤ O) (h : W ≤ ρ ⁻¹ᵁ O) (h' : W' ≤ ρ ⁻¹ᵁ O') (a : Γ(Y, O)) :
    resG Y' hW ((ρ.appLE O W h).hom a) = (ρ.appLE O' W' h').hom (resG Y hO a) := by sorry
