-- Prove2me | Theorems.Thm_GlobalTheory_UnifPullRig_compatAlong_of_square
-- name    : GlobalTheory.UnifPullRig.compatAlong_of_square
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:25:03.935141+00:00
-- url     : https://prove2.me/theorems/11dd0fae-05e0-44b7-a0dd-63948e083d2d
-- title:
--   Unif Pull Rig: compat Along of square
-- statement:
--   The Unif Pull Rig construction uses the compat Along of square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CompatAlongOfSquare.lean#L86-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CompatAlongOfSquare.lean#L86-L105

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CompatAlongOfSquare
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
noncomputable section
open GlobalTheory
open GlobalTheory.UnifPullRig
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S S' B B' T T' T₁ T₁' G G' A A' : Scheme.{0}}
variable {L : LB G} {M : LB A} {L' : LB G'} {M' : LB A'} {F : G' ⟶ G} {E : A' ⟶ A}
    {f : T ⟶ G} {p : T ⟶ A} {f' : T' ⟶ G'} {p' : T' ⟶ A'}
    {f₁ : T₁ ⟶ G} {p₁ : T₁ ⟶ A} {f₁' : T₁' ⟶ G'} {p₁' : T₁' ⟶ A'}

theorem GlobalTheory.UnifPullRig.compatAlong_of_square (hL : L.IsLB) (hM : M.IsLB)
    {wL : LB.Iso L' (L.pull F)} {wM : LB.Iso M' (M.pull E)}
    {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f') (M'.pull p')} {h : T' ⟶ T}
    {w₁ : LB.Iso (L.pull f₁) (M.pull p₁)} {w₁' : LB.Iso (L'.pull f₁') (M'.pull p₁')} {h₁ : T₁' ⟶ T₁}
    {m : T ⟶ T₁} {m' : T' ⟶ T₁'} (Q : Square wL wM w w' h) (Q₁ : Square wL wM w₁ w₁' h₁)
    (H : CompatAlong w₁ w m) (hf : m ≫ f₁ = f) (hp : m ≫ p₁ = p) (hf' : m' ≫ f₁' = f')
    (hp' : m' ≫ p₁' = p') (hF : h ≫ f = f' ≫ F) (hE : p' ≫ E = h ≫ p) (hm : m' ≫ h₁ = h ≫ m) :
    CompatAlong w₁' w' m' := by sorry
