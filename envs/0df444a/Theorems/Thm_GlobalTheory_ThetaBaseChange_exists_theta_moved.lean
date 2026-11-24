-- Prove2me | Theorems.Thm_GlobalTheory_ThetaBaseChange_exists_theta_moved
-- name    : GlobalTheory.ThetaBaseChange.exists_theta_moved
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:05:29.075769+00:00
-- url     : https://prove2.me/theorems/b7044d1d-87b8-417e-849d-5a4f5cc5a85a
-- title:
--   Theta Base Change: exists theta moved
-- statement:
--   The Theta Base Change construction uses the exists theta moved property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PowEqOneOfPush.lean#L276-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PowEqOneOfPush.lean#L276-L323

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
  {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {Φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}

theorem GlobalTheory.ThetaBaseChange.exists_theta_moved (hL : L.IsLB) (hL' : L'.IsLB) (ht : t' ≫ g = t) (hp : IsGrpPullback A' A g Φ)
    {v : LB.Iso L' (L.pull Φ)} (hv : PGen v) {ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left}
    (h₁ : ω ≫ (fst (Over.mk t') A').left = (fst (Over.mk t) A).left)
    (h₂ : ω ≫ (snd (Over.mk t') A').left ≫ Φ = (snd (Over.mk t) A).left) {k : ℤ}
    (θ' : ThetaGrp A' L' k (Over.mk t')) {x : Over.mk t ⟶ A} (hx : θ'.pt.left ≫ Φ = x.left) :
    ∃ θ : ThetaGrp A L k (Over.mk t), θ.pt = x ∧ ∀ s' s₂' s s₂, Moved v ω s' s → Moved v ω s₂' s₂ →
      IsActOf A' L' k θ' s' s₂' → IsActOf A L k θ s s₂ := by sorry
