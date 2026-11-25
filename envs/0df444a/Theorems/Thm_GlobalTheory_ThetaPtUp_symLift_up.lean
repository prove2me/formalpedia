-- Prove2me | Theorems.Thm_GlobalTheory_ThetaPtUp_symLift_up
-- name    : GlobalTheory.ThetaPtUp.symLift_up
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:46:11.729817+00:00
-- url     : https://prove2.me/theorems/14b1877b-4d36-4dcd-9544-930ffc1b263f
-- title:
--   Theta Pt Up: sym Lift up
-- statement:
--   The Theta Pt Up construction uses the sym Lift up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HasThetaConstantsIffOfThetaLevelPullback.lean#L118-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HasThetaConstantsIffOfThetaLevelPullback.lean#L118-L189

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

theorem GlobalTheory.ThetaPtUp.symLift_up [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {k : ℤ} {n : ℕ} {x : T ⟶ A}
    {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x ^ n = 1) {θ : ThetaGrp A L₁ k T}
    (H₁ : SymLift A L₁ k n x θ) : ∃ θ₀ : ThetaGrp G L₀ k T₀, SymLift G L₀ k n x₀ θ₀ ∧
      ∀ s₀ s₀' s s', SecRel hp τ hτ w s s₀ → SecRel hp τ hτ w s' s₀' → IsActOf A L₁ k θ s s' →
        IsActOf G L₀ k θ₀ s₀ s₀' := by sorry
