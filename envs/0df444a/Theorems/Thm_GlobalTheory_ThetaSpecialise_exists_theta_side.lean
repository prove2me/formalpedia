-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSpecialise_exists_theta_side
-- name    : GlobalTheory.ThetaSpecialise.exists_theta_side
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:22:25.512179+00:00
-- url     : https://prove2.me/theorems/a672a9d6-9857-415b-97bd-a6b243de9d62
-- title:
--   Theta Specialise: exists theta side
-- statement:
--   The Theta Specialise construction uses the exists theta side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsFOfIntegral.lean#L120-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsFOfIntegral.lean#L120-L159

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMoveMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsFOfIntegral
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
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange
variable {S₀ S₁ : Scheme.{0}} {G : Over S₀} [GrpObj G] {A : Over S₁} [GrpObj A]
  {f : S₁ ⟶ S₀} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S₁} {T₀ : Over S₀} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}

theorem GlobalTheory.ThetaSpecialise.exists_theta_side (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) (k : ℤ)
    (x : T ⟶ A) (θ₀ : ThetaGrp G L₀ k T₀) (hx : τ ≫ θ₀.pt.left = x.left ≫ φ)
    {ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left} (hψ : ψ = (psiO hp τ hτ).left) :
    ∃ θ : ThetaGrp A L₁ k T, θ.pt = x ∧ ∀ (s₀ s₀' : LB.Sec (LPow G L₀ k T₀)) (s s' : LB.Sec (LPow A L₁ k T)),
      PSec w (fun _ : Fin 1 => (snd T A).left) (fun _ => (snd T₀ G).left) (fun _ => k) ψ s s₀ →
      PSec w (fun _ : Fin 1 => (snd T A).left) (fun _ => (snd T₀ G).left) (fun _ => k) ψ s' s₀' →
      IsActOf G L₀ k θ₀ s₀ s₀' → IsActOf A L₁ k θ s s' := by sorry
