-- Prove2me | Theorems.Thm_GlobalTheory_ToricData_unitOn_zpow
-- name    : GlobalTheory.ToricData.unitOn_zpow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:21:15.076209+00:00
-- url     : https://prove2.me/theorems/01ac063e-d80e-5655-b320-36b9510d218d
-- title:
--   Toric Data: unit On zpow
-- statement:
--   The Toric Data construction uses the unit On zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/PsiWeightZeroLinearCombination.lean#L123-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/PsiWeightZeroLinearCombination.lean#L123-L125

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
variable {A B : Type} [CommRing A] [CommRing B]

theorem GlobalTheory.ToricData.unitOn_zpow (u : Aˣ) (n : ℤ) : unitOn (u ^ n) = unitOn u ^ n := by sorry
