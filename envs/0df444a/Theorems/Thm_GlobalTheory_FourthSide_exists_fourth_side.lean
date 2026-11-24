-- Prove2me | Theorems.Thm_GlobalTheory_FourthSide_exists_fourth_side
-- name    : GlobalTheory.FourthSide.exists_fourth_side
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:35.797873+00:00
-- url     : https://prove2.me/theorems/7abe60b8-7641-4b68-bae4-3fc903605f24
-- title:
--   Fourth Side: exists fourth side
-- statement:
--   The Fourth Side construction uses the exists fourth side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFourthSide.lean#L110-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFourthSide.lean#L110-L133

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFourthSide
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FourthSide
variable {B B' G G' Ge Ge' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {L' : LB G'}
  {Φ : B' ⟶ B} {Ψ : G' ⟶ G} {pG : Ge ⟶ B} {pG' : Ge' ⟶ B'} {fG : Ge ⟶ G} {fG' : Ge' ⟶ G'} {h : Ge' ⟶ Ge}

theorem GlobalTheory.FourthSide.exists_fourth_side (B B' G G' Ge Ge' : Scheme.{0}) (M : LB B) (M' : LB B') (L : LB G) (L' : LB G')
    (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB) (Φ : B' ⟶ B) (Ψ : G' ⟶ G) (pG : Ge ⟶ B)
    (pG' : Ge' ⟶ B') (fG : Ge ⟶ G) (fG' : Ge' ⟶ G') (h : Ge' ⟶ Ge) (e₁ : pG' ≫ Φ = h ≫ pG)
    (e₂ : h ≫ fG = fG' ≫ Ψ) (w : LB.Iso M' (M.pull Φ)) (wL : LB.Iso L' (L.pull Ψ))
    (we : LB.Iso (L.pull fG) (M.pull pG)) (hw : w.IsGen) (hwL : wL.IsGen) (hwe : we.IsGen) :
    ∃ we' : LB.Iso (L'.pull fG') (M'.pull pG'), we'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
        Φ (pG' (r z)) ∈ M.U jM → pG' (r z) ∈ M'.U jM' → Ψ (fG' (r z)) ∈ L.U jL → fG' (r z) ∈ L'.U jL' →
        gw w (r ≫ pG') z jM jM' * gw we' r z jM' (fun _ => jL') =
          gw we (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ fG') z jL jL' := by sorry
