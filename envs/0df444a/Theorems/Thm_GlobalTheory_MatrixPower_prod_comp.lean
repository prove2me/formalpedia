-- Prove2me | Theorems.Thm_GlobalTheory_MatrixPower_prod_comp
-- name    : GlobalTheory.MatrixPower.prod_comp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:21:40.652805+00:00
-- url     : https://prove2.me/theorems/3f499bd7-374c-40cd-948b-956a6f2c2ee9
-- title:
--   Matrix Power: prod comp
-- statement:
--   The Matrix Power construction uses the prod comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AbelianSchemeEighthPowerOfMatrixAction.lean#L95-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AbelianSchemeEighthPowerOfMatrixAction.lean#L95-L101

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

theorem GlobalTheory.MatrixPower.prod_comp {n : Type*} (s : Finset n) {T G H : C} [GrpObj G] [IsCommMonObj G]
    [GrpObj H] [IsCommMonObj H] (g : n → (T ⟶ G)) (f : G ⟶ H) [IsMonHom f] :
    (∏ u ∈ s, g u) ≫ f = ∏ u ∈ s, g u ≫ f := by sorry
