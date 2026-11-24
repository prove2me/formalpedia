-- Prove2me | Theorems.Thm_GlobalTheory_WeilPull_commIsOf_iff_of_rel
-- name    : GlobalTheory.WeilPull.commIsOf_iff_of_rel
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:55:20.078955+00:00
-- url     : https://prove2.me/theorems/6680ba89-c9aa-4982-b555-aee803e359fb
-- title:
--   Weil Pull: comm Is Of iff of rel
-- statement:
--   The Weil Pull construction uses the comm Is Of iff of rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/WeilIsGrpPullbackOfCommute.lean#L131-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/WeilIsGrpPullbackOfCommute.lean#L131-L170

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
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
open GlobalTheory GlobalTheory.WeilPull
open GlobalTheory.CommPairing
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {k : ℤ}

theorem GlobalTheory.WeilPull.commIsOf_iff_of_rel [IsIso τ] (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ))
    {θx θy : ThetaGrp A L₁ k T} {θx₀ θy₀ : ThetaGrp G L₀ k T₀} (hc : θx.pt * θy.pt = θy.pt * θx.pt)
    (hx : τ ≫ θx₀.pt.left = θx.pt.left ≫ φ) (hy : τ ≫ θy₀.pt.left = θy.pt.left ≫ φ)
    (mx : Rel hp τ hτ w θx θx₀) (my : Rel hp τ hτ w θy θy₀) (c₀ : Γ(T₀.left, ⊤)ˣ) (c : Γ(T.left, ⊤)ˣ)
    (hcc : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z), gm (r ≫ τ) z ⊤ c₀ = gm r z ⊤ c) :
    CommIsOf A L₁ k θx θy c ↔ CommIsOf G L₀ k θx₀ θy₀ c₀ := by sorry
