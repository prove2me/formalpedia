-- Prove2me | Theorems.Thm_GlobalTheory_UnifZero_secScal_iff
-- name    : GlobalTheory.UnifZero.secScal_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:03:03.749498+00:00
-- url     : https://prove2.me/theorems/badfff38-0cab-4cea-8395-bddaa3202a4f
-- title:
--   Unif Zero: sec Scal iff
-- statement:
--   The Unif Zero construction uses the sec Scal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecEqOfSecConst.lean#L94-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecEqOfSecConst.lean#L94-L104

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

theorem GlobalTheory.UnifZero.secScal_iff {φ₁ : J → (Y' ⟶ X)} {ε₁ : J → ℤ} {s₁ : LB.Sec (LB.LinComb (trivLB X) φ₁ ε₁)}
    {φ₂ : J' → (Y ⟶ X)} {ε₂ : J' → ℤ} {s₂ : LB.Sec (LB.LinComb (trivLB X) φ₂ ε₂)} {a : Γ(Y', ⊤)}
    {b : Γ(Y, ⊤)} (ha : SecConst s₁ a) (hb : SecConst s₂ b) (h : Y' ⟶ Y) (c : Γ(Y', ⊤)) :
    GeneratorPullback.SecScal (trivLB X) φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c ↔ h.appTop.hom b = c * a := by sorry
