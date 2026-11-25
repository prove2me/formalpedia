-- Prove2me | Theorems.Thm_GlobalTheory_ThetaPtMove_symLift_move
-- name    : GlobalTheory.ThetaPtMove.symLift_move
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:36:11.069456+00:00
-- url     : https://prove2.me/theorems/d9b7eacc-43a2-5ed5-9a1d-c37c1a1f1865
-- title:
--   Theta Pt Move: sym Lift move
-- statement:
--   The Theta Pt Move construction uses the sym Lift move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverMove.lean#L195-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverMove.lean#L195-L264

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

theorem GlobalTheory.ThetaPtMove.symLift_move [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {k : ℤ} {n : ℕ} {x : T ⟶ A}
    {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x ^ n = 1) {θ₀ : ThetaGrp G L₀ k T₀}
    (H₀ : SymLift G L₀ k n x₀ θ₀) : ∃ θ : ThetaGrp A L₁ k T, SymLift A L₁ k n x θ ∧
      ∀ s₀ s₀' s s', SecRel hp τ hτ w s s₀ → SecRel hp τ hτ w s' s₀' → IsActOf G L₀ k θ₀ s₀ s₀' →
        IsActOf A L₁ k θ s s' := by sorry
