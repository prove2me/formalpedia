-- Prove2me | Theorems.Thm_GlobalTheory_square_res_iff_gw
-- name    : GlobalTheory.square_res_iff_gw
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:22:41.17543+00:00
-- url     : https://prove2.me/theorems/111ae6bd-6819-4935-b28d-bf1ec0fa0021
-- title:
--   Global Theory: square res iff gw
-- statement:
--   The Global Theory construction uses the square res iff gw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GmMulEqOfResMulEq.lean#L35-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GmMulEqOfResMulEq.lean#L35-L74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmMulEqOfResMulEq
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
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.square_res_iff_gw {X X' G G' Y Y' : Scheme.{0}} {M : LB X} {M' : LB X'} {L : LB G} {L' : LB G'}
    {F : X' ⟶ X} {B : G' ⟶ G} {p : Y ⟶ X} {p' : Y' ⟶ X'} {f : Y ⟶ G} {f' : Y' ⟶ G'} {h : Y' ⟶ Y}
    (hf : h ≫ f = f' ≫ B) (hp : p' ≫ F = h ≫ p)
    (wM : LB.Iso M' (M.pull F)) (wL : LB.Iso L' (L.pull B))
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p')) :
    (∀ (jM : PUnit → M.ι) (jM' : M'.ι) (jL' : L'.ι) (jL : PUnit → L.ι),
      res (X := Y') (inf_le_left.trans (inf_le_left.trans inf_le_left) :
          p' ⁻¹ᵁ (LB.div (M.pull F) M').U (jM, jM') ⊓
            (LB.div (M'.pull p') (L'.pull f')).U (fun _ => jM', fun _ => jL') ⊓
            h ⁻¹ᵁ (LB.div (M.pull p) (L.pull f)).U (jM, jL) ⊓
            f' ⁻¹ᵁ (LB.div (L.pull B) L').U (jL, jL') ≤
          p' ⁻¹ᵁ (LB.div (M.pull F) M').U (jM, jM'))
        (pullU p' _ (wM.s (jM, jM'))) *
      res (X := Y') (inf_le_left.trans (inf_le_left.trans inf_le_right))
        (w'.s (fun _ => jM', fun _ => jL')) =
      res (X := Y') (inf_le_left.trans inf_le_right) (pullU h _ (w.s (jM, jL))) *
      res (X := Y') inf_le_right (pullU f' _ (wL.s (jL, jL')))) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
      F (p' (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → B (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
      gw wM (r ≫ p') z jM jM' * gw w' r z jM' (fun _ => jL') =
        gw w (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ f') z jL jL' := by sorry
