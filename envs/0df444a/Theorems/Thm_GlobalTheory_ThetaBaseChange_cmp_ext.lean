-- Prove2me | Theorems.Thm_GlobalTheory_ThetaBaseChange_cmp_ext
-- name    : GlobalTheory.ThetaBaseChange.cmp_ext
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:59:35.496048+00:00
-- url     : https://prove2.me/theorems/a19f4686-6ed1-4fa5-9d81-6c8aee1ee7be
-- title:
--   Theta Base Change: cmp ext
-- statement:
--   The Theta Base Change construction uses the cmp ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PowEqOneOfPush.lean#L124-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PowEqOneOfPush.lean#L124-L148

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
variable {S S' W : Scheme.{0}} {g : S' ⟶ S} {t : W ⟶ S} {t' : W ⟶ S'}

theorem GlobalTheory.ThetaBaseChange.cmp_ext {A : Over S} {A' : Over S'} {Φ : A'.left ⟶ A.left} (hp : IsPullback Φ A'.hom A.hom g)
    {Z : Scheme.{0}} {a b : Z ⟶ (Over.mk t' ⊗ A').left}
    (h₁ : a ≫ (fst (Over.mk t') A').left = b ≫ (fst (Over.mk t') A').left)
    (h₂ : a ≫ (snd (Over.mk t') A').left ≫ Φ = b ≫ (snd (Over.mk t') A').left ≫ Φ) : a = b := by sorry
