-- Prove2me | Theorems.Thm_GlobalTheory_UnifPullRig_CompatAlong_stalk
-- name    : GlobalTheory.UnifPullRig.CompatAlong.stalk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:49.03987+00:00
-- url     : https://prove2.me/theorems/9a8a9c5f-fb5c-423c-8f4b-4b0fbf239594
-- title:
--   Compat Along: stalk
-- statement:
--   The Compat Along construction uses the stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CompatAlongOfSquare.lean#L75-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CompatAlongOfSquare.lean#L75-L84

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

theorem GlobalTheory.UnifPullRig.CompatAlong.stalk {w₁ : LB.Iso (L.pull f₁) (M.pull p₁)} {w : LB.Iso (L.pull f) (M.pull p)}
    {m : T ⟶ T₁} (H : CompatAlong w₁ w m) (hf : m ≫ f₁ = f) (hp : m ≫ p₁ = p) {Z : Scheme.{0}}
    (r : Z ⟶ T) (z : Z) (jM : M.ι) (jL : L.ι) (hM : p (r z) ∈ M.U jM) (hL : f (r z) ∈ L.U jL) :
    gw w₁ (r ≫ m) z jM (fun _ => jL) = gw w r z jM (fun _ => jL) := by sorry
