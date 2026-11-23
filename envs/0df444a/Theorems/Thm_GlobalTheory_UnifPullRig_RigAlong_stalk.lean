-- Prove2me | Theorems.Thm_GlobalTheory_UnifPullRig_RigAlong_stalk
-- name    : GlobalTheory.UnifPullRig.RigAlong.stalk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:39.230477+00:00
-- url     : https://prove2.me/theorems/98ae35e7-fffb-4175-be3d-86048fa5da5a
-- title:
--   Rig Along: stalk
-- statement:
--   The Rig Along construction uses the stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CompatAlongOfSquare.lean#L60-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CompatAlongOfSquare.lean#L60-L73

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

theorem GlobalTheory.UnifPullRig.RigAlong.stalk {w : LB.Iso (L.pull f) (M.pull p)} {ε : S ⟶ T} {i : S ⟶ B} {eG : B ⟶ G}
    {eA : B ⟶ A} {rL : LB.Gen (L.pull eG)} {rM : LB.Gen (M.pull eA)} (H : RigAlong w ε i rL rM)
    (hf : ε ≫ f = i ≫ eG) (hp : ε ≫ p = i ≫ eA) {Z : Scheme.{0}} (r : Z ⟶ S) (z : Z) (jM : M.ι)
    (jL : L.ι) (hM : p (ε (r z)) ∈ M.U jM) (hL : f (ε (r z)) ∈ L.U jL) :
    gw w (r ≫ ε) z jM (fun _ => jL) * gm (r ≫ i) z ((L.pull eG).U (fun _ => jL)) (rL.s (fun _ => jL)) =
      gm (r ≫ i) z ((M.pull eA).U (fun _ => jM)) (rM.s (fun _ => jM)) := by sorry
