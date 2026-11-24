-- Prove2me | Theorems.Thm_GlobalTheory_PsiUnitOfPsiOn_injective_of_isIso
-- name    : GlobalTheory.PsiUnitOfPsiOn.injective_of_isIso
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:57:02.049014+00:00
-- url     : https://prove2.me/theorems/5c765be9-1000-4b33-a5e0-7e613a901b6d
-- title:
--   Psi Unit Of Psi On: injective of is Iso
-- statement:
--   The Psi Unit Of Psi On construction uses the injective of is Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PsiUnitOnOfPsiOn.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PsiUnitOnOfPsiOn.lean#L14-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PsiUnitOnOfPsiOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Semi CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PsiUnitOfPsiOn

theorem GlobalTheory.PsiUnitOfPsiOn.injective_of_isIso {A B : CommRingCat} (f : A ⟶ B) [IsIso f] : Function.Injective f.hom := by sorry
