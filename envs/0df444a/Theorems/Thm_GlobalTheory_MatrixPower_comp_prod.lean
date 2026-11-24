-- Prove2me | Theorems.Thm_GlobalTheory_MatrixPower_comp_prod
-- name    : GlobalTheory.MatrixPower.comp_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:21:42.202804+00:00
-- url     : https://prove2.me/theorems/f1b13b4a-bbb5-4646-9e5b-7618295e96d3
-- title:
--   Matrix Power: comp prod
-- statement:
--   The Matrix Power construction uses the comp prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AbelianSchemeEighthPowerOfMatrixAction.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AbelianSchemeEighthPowerOfMatrixAction.lean#L88-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AbelianSchemeEighthPowerOfMatrixAction
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.MatrixPower
variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
variable [BraidedCategory C]

theorem GlobalTheory.MatrixPower.comp_prod {n : Type*} (s : Finset n) {T X G : C} [GrpObj G] [IsCommMonObj G]
    (f : T ⟶ X) (g : n → (X ⟶ G)) : f ≫ ∏ u ∈ s, g u = ∏ u ∈ s, f ≫ g u := by sorry
