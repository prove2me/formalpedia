-- Prove2me | Theorems.Thm_GlobalTheory_ThetaPtUp_isThetaPtOver_up
-- name    : GlobalTheory.ThetaPtUp.isThetaPtOver_up
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:46:40.397663+00:00
-- url     : https://prove2.me/theorems/b06aaf27-a524-4859-bec6-b03dfd1ec670
-- title:
--   Theta Pt Up: is Theta Pt Over up
-- statement:
--   The Theta Pt Up construction uses the is Theta Pt Over up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HasThetaConstantsIffOfThetaLevelPullback.lean#L191-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HasThetaConstantsIffOfThetaLevelPullback.lean#L191-L213

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HasThetaConstantsIffOfThetaLevelPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ThetaPtUp
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift GlobalTheory.ThetaPtMove
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) [IsIso τ] (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}

theorem GlobalTheory.ThetaPtUp.isThetaPtOver_up {P₀ : PolAV S} {P : PolAV S'} {φ : P.A.left ⟶ P₀.A.left}
    (hp : IsGrpPullback P.A P₀.A f φ) (hw : LBIso P.L (P₀.L.pull φ)) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
    {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {x₀ : I → (T₀ ⟶ P₀.A)} (hx : ∀ i, τ ≫ (x₀ i).left = (x i).left ≫ φ)
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {v : I → Γ(T.left, ⊤)} (H : IsThetaPtOver P k x v) :
    IsThetaPtOver P₀ k x₀ (fun i => (inv τ).appTop.hom (v i)) := by sorry
