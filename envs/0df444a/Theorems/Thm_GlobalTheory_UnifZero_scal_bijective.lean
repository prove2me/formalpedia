-- Prove2me | Theorems.Thm_GlobalTheory_UnifZero_scal_bijective
-- name    : GlobalTheory.UnifZero.scal_bijective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:09:55.306135+00:00
-- url     : https://prove2.me/theorems/1de0da12-df29-569d-ae81-fa4885da245c
-- title:
--   Unif Zero: scal bijective
-- statement:
--   The Unif Zero construction uses the scal bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecEqOfSecConst.lean#L134-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecEqOfSecConst.lean#L134-L136

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.UnifZero
open GlobalTheory.ToricData
variable {X Y Y' : Scheme.{0}} {J J' J'' : Type} [Fintype J] [Fintype J'] [Fintype J'']
variable {A B : Type} [CommRing A] [CommRing B]

theorem GlobalTheory.UnifZero.scal_bijective (p : Y ⟶ Spec (CommRingCat.of A)) [IsIso p] : Function.Bijective (scal p) := by sorry
