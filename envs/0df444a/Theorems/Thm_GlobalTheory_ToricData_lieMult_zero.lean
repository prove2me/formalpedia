-- Prove2me | Theorems.Thm_GlobalTheory_ToricData_lieMult_zero
-- name    : GlobalTheory.ToricData.lieMult_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:24:47.3158+00:00
-- url     : https://prove2.me/theorems/53455daf-e7d6-5ec9-b2db-f215d253cde5
-- title:
--   Toric Data: lie Mult zero
-- statement:
--   The Toric Data construction uses the lie Mult zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/PsiWeightZeroLinearCombination.lean#L283-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/PsiWeightZeroLinearCombination.lean#L283-L286

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ToricData
variable (K : Type) [CommRing K] [IsDomain K] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable {K X}
variable (q : X → (FractionRing K)ˣ)

theorem GlobalTheory.ToricData.lieMult_zero (O : Type) [CommRing O] [StarRing O] [Module O X] (h) {F : Type} [Field F] (f : K →+* F)
    (τ : O →+* F) :
    LieMult (ofRingAct (toricOAct q O h).onB.toRingAct) (spMap f) τ 0 := by sorry
