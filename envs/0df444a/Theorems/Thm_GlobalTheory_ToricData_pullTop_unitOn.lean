-- Prove2me | Theorems.Thm_GlobalTheory_ToricData_pullTop_unitOn
-- name    : GlobalTheory.ToricData.pullTop_unitOn
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:20:57.806811+00:00
-- url     : https://prove2.me/theorems/7eb170cd-701d-4b13-8540-806e1001105b
-- title:
--   Toric Data: pull Top unit On
-- statement:
--   The Toric Data construction uses the pull Top unit On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/PsiWeightZeroLinearCombination.lean#L142-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/PsiWeightZeroLinearCombination.lean#L142-L147

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

theorem GlobalTheory.ToricData.pullTop_unitOn (f : A →+* B) (u : Aˣ) :
    pullTop (Spec.map (CommRingCat.ofHom f)) (unitOn u) = unitOn (Units.map f.toMonoidHom u) := by sorry
