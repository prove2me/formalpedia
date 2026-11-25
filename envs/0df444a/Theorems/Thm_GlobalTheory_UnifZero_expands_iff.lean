-- Prove2me | Theorems.Thm_GlobalTheory_UnifZero_expands_iff
-- name    : GlobalTheory.UnifZero.expands_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:02:38.273211+00:00
-- url     : https://prove2.me/theorems/f4d7f9a3-243c-4877-8a67-7717154d4efb
-- title:
--   Unif Zero: expands iff
-- statement:
--   The Unif Zero construction uses the expands iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecEqOfSecConst.lean#L278-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecEqOfSecConst.lean#L278-L318

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
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R)
variable {R I}

theorem GlobalTheory.UnifZero.expands_iff [IsHausdorff I R] (k : ℕ) {s : (zeroPre R I).SecK k}
    {F : Fam (zeroData R I).toPre (FractionRing R) k} {x y : FractionRing R}
    (hs : SecConst s (scal pGK x)) (hF : SecConst (F.s PUnit.unit) (scal pBK y)) :
    (zeroPre R I).Expands k s F ↔ x = y := by sorry
