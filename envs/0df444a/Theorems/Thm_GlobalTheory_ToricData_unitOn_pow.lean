-- Prove2me | Theorems.Thm_GlobalTheory_ToricData_unitOn_pow
-- name    : GlobalTheory.ToricData.unitOn_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:37:48.792849+00:00
-- url     : https://prove2.me/theorems/845ed368-6634-415d-8b75-e033a533b772
-- title:
--   Toric Data: unit On pow
-- statement:
--   The Toric Data construction uses the unit On pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/PsiWeightZeroLinearCombination.lean#L127-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/PsiWeightZeroLinearCombination.lean#L127-L129

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

theorem GlobalTheory.ToricData.unitOn_pow (u : Aˣ) (n : ℕ) : unitOn (u ^ n) = unitOn u ^ n := by sorry
