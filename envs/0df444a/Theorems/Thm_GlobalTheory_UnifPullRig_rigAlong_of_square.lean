-- Prove2me | Theorems.Thm_GlobalTheory_UnifPullRig_rigAlong_of_square
-- name    : GlobalTheory.UnifPullRig.rigAlong_of_square
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:24:59.647733+00:00
-- url     : https://prove2.me/theorems/030d7e98-f015-4a1b-8760-5ca1c4ff8c86
-- title:
--   Unif Pull Rig: rig Along of square
-- statement:
--   The Unif Pull Rig construction uses the rig Along of square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CompatAlongOfSquare.lean#L107-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CompatAlongOfSquare.lean#L107-L141

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

theorem GlobalTheory.UnifPullRig.rigAlong_of_square (hL : L.IsLB) (hM : M.IsLB)
    {wL : LB.Iso L' (L.pull F)} {wM : LB.Iso M' (M.pull E)}
    {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f') (M'.pull p')} {h : T' ⟶ T}
    {ε : S ⟶ T} {i : S ⟶ B} {eG : B ⟶ G} {eA : B ⟶ A} {rL : LB.Gen (L.pull eG)}
    {rM : LB.Gen (M.pull eA)}
    {ε' : S' ⟶ T'} {i' : S' ⟶ B'} {eG' : B' ⟶ G'} {eA' : B' ⟶ A'} {rL' : LB.Gen (L'.pull eG')}
    {rM' : LB.Gen (M'.pull eA')} {b : B' ⟶ B} {σ : S' ⟶ S}
    (Q : Square wL wM w w' h) (H : RigAlong w ε i rL rM)
    (PL : PMaps wL (K := PUnit) (fun _ => eG') (fun _ => eG) (fun _ => 1) rL' rL b)
    (PM : PMaps wM (K := PUnit) (fun _ => eA') (fun _ => eA) (fun _ => 1) rM' rM b)
    (hf : ε ≫ f = i ≫ eG) (hp : ε ≫ p = i ≫ eA) (hf' : ε' ≫ f' = i' ≫ eG') (hp' : ε' ≫ p' = i' ≫ eA')
    (hF : h ≫ f = f' ≫ F) (hE : p' ≫ E = h ≫ p) (hε : ε' ≫ h = σ ≫ ε) (hσ : σ ≫ i = i' ≫ b) :
    RigAlong w' ε' i' rL' rM' := by sorry
