-- Prove2me | Theorems.Thm_GlobalTheory_ThetaPtMove_isValueAt_move
-- name    : GlobalTheory.ThetaPtMove.isValueAt_move
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:37:20.697992+00:00
-- url     : https://prove2.me/theorems/2885f053-dad3-5be5-854f-b10be7078083
-- title:
--   Theta Pt Move: is Value At move
-- statement:
--   The Theta Pt Move construction uses the is Value At move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverMove.lean#L182-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverMove.lean#L182-L193

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaPtMove
open GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
variable {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}

theorem GlobalTheory.ThetaPtMove.isValueAt_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {x : T ⟶ A} {x₀ : T₀ ⟶ G}
    (hx : τ ≫ x₀.left = x.left ≫ φ)
    {ρ₀ : LB.Gen (LB.LinComb L₀ (Y := T₀.left) (K := Fin 1) (fun _ => x₀.left) (fun _ => a))}
    {ρ : LB.Gen (LB.LinComb L₁ (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))}
    (H : GenThrough w _ _ _ ρ ρ₀ τ) {s₀ s} (hs : SecRel hp τ hτ w s s₀) {c : Γ(T₀.left, ⊤)}
    (H₀ : IsValueAt G L₀ a s₀ x₀ ρ₀ c) : IsValueAt A L₁ a s x ρ (τ.appTop.hom c) := by sorry
