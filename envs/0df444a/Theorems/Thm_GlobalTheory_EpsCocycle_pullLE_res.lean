-- Prove2me | Theorems.Thm_GlobalTheory_EpsCocycle_pullLE_res
-- name    : GlobalTheory.EpsCocycle.pullLE_res
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:58:31.960444+00:00
-- url     : https://prove2.me/theorems/26fe8625-b1aa-4d3a-a7a0-1736387e6fa8
-- title:
--   Eps Cocycle: pull LE res
-- statement:
--   The Eps Cocycle construction uses the pull LE res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleCocycleOneAddEps.lean#L154-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleCocycleOneAddEps.lean#L154-L158

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleCocycleOneAddEps
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
open GlobalTheory GlobalTheory.EpsCocycle
noncomputable section

theorem GlobalTheory.EpsCocycle.pullLE_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U')
    (h' : U' ≤ U) (h'' : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) : pullLE f h (res h' x) = pullLE f h'' x := by sorry
