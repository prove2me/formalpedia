-- Prove2me | Theorems.Thm_GlobalTheory_DualRigidity_eq_comp_section_of_const
-- name    : GlobalTheory.DualRigidity.eq_comp_section_of_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:17:57.591589+00:00
-- url     : https://prove2.me/theorems/e0d8c406-39a3-4ef2-bce5-df96b308728f
-- title:
--   Dual Rigidity: eq comp section of const
-- statement:
--   The Dual Rigidity construction uses the eq comp section of const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SubsingletonSpDualNumber.lean#L15-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SubsingletonSpDualNumber.lean#L15-L27

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

theorem GlobalTheory.DualRigidity.eq_comp_section_of_const {X T Y : Scheme.{0}} (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y)
    (h : ε ≫ p = 𝟙 T) (hs : Function.Surjective p.appTop.hom) (y : Y) (hy : ∀ x : X, g x = y) :
    g = p ≫ ε ≫ g := by sorry
