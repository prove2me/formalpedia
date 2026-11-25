-- Prove2me | Theorems.Thm_GlobalTheory_PsiUnitOfPsiOn_psiUnitOn_of_psiOn
-- name    : GlobalTheory.PsiUnitOfPsiOn.psiUnitOn_of_psiOn
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:16:54.786426+00:00
-- url     : https://prove2.me/theorems/1811397f-c2af-4404-a623-3460dcc467fb
-- title:
--   Psi Unit Of Psi On: psi Unit On of psi On
-- statement:
--   The Psi Unit Of Psi On construction uses the psi Unit On of psi On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PsiUnitOnOfPsiOn.lean#L23-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PsiUnitOnOfPsiOn.lean#L23-L66

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

theorem GlobalTheory.PsiUnitOfPsiOn.psiUnitOn_of_psiOn : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Spec (CommRingCat.of R)).Opens), PsiOn D W → ∀ y : D.X, PsiUnitOn D y (W : Set (Spec (CommRingCat.of R))) := by sorry
