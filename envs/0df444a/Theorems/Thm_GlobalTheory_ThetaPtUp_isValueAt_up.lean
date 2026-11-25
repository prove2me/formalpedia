-- Prove2me | Theorems.Thm_GlobalTheory_ThetaPtUp_isValueAt_up
-- name    : GlobalTheory.ThetaPtUp.isValueAt_up
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:40:57.363243+00:00
-- url     : https://prove2.me/theorems/d9a72683-096e-44a1-a736-2d8e1d72c7ea
-- title:
--   Theta Pt Up: is Value At up
-- statement:
--   The Theta Pt Up construction uses the is Value At up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HasThetaConstantsIffOfThetaLevelPullback.lean#L84-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HasThetaConstantsIffOfThetaLevelPullback.lean#L84-L96

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

theorem GlobalTheory.ThetaPtUp.isValueAt_up (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {x : T ⟶ A} {x₀ : T₀ ⟶ G}
    (hx : τ ≫ x₀.left = x.left ≫ φ)
    {ρ₀ : LB.Gen (LB.LinComb L₀ (Y := T₀.left) (K := Fin 1) (fun _ => x₀.left) (fun _ => a))}
    {ρ : LB.Gen (LB.LinComb L₁ (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))}
    (H : GenThrough w _ _ _ ρ ρ₀ τ) {s₀ s} (hs : SecRel hp τ hτ w s s₀) {c : Γ(T.left, ⊤)}
    (H₁ : IsValueAt A L₁ a s x ρ c) : IsValueAt G L₀ a s₀ x₀ ρ₀ ((inv τ).appTop.hom c) := by sorry
