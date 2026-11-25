-- Prove2me | Theorems.Thm_GlobalTheory_ThetaPtUp_exists_genThrough_up
-- name    : GlobalTheory.ThetaPtUp.exists_genThrough_up
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:40:06.693669+00:00
-- url     : https://prove2.me/theorems/1bce00ea-f821-417b-923c-aa69320672b3
-- title:
--   Theta Pt Up: exists gen Through up
-- statement:
--   The Theta Pt Up construction uses the exists gen Through up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HasThetaConstantsIffOfThetaLevelPullback.lean#L46-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HasThetaConstantsIffOfThetaLevelPullback.lean#L46-L61

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

theorem GlobalTheory.ThetaPtUp.exists_genThrough_up (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a b : ℤ} {m : T ⊗ A ⟶ A}
    {m₀ : T₀ ⊗ G ⟶ G} (h : psi hp τ hτ ≫ m₀.left = m.left ≫ φ)
    (α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, m.left] ![a, b])) (hα : α.IsGen) :
    ∃ α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, m₀.left] ![a, b]), α₀.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
        val α₀ (r ≫ psi hp τ hτ) z J =
          (wVal w z J J' (r ≫ (snd T A).left) ^ a * wVal w z J J' (r ≫ m.left) ^ b) * val α r z J' := by sorry
