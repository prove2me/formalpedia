-- Prove2me | Theorems.Thm_GlobalTheory_FourthSide_exists_unit
-- name    : GlobalTheory.FourthSide.exists_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:17.671027+00:00
-- url     : https://prove2.me/theorems/35640355-6041-4e92-a2f9-24cadbdc7ebc
-- title:
--   Fourth Side: exists unit
-- statement:
--   The Fourth Side construction uses the exists unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFourthSide.lean#L63-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFourthSide.lean#L63-L108

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

theorem GlobalTheory.FourthSide.exists_unit (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB)
    (e₁ : pG' ≫ Φ = h ≫ pG) (e₂ : h ≫ fG = fG' ≫ Ψ) {w : LB.Iso M' (M.pull Φ)}
    {wL : LB.Iso L' (L.pull Ψ)} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : PGen w) (hwL : PGen wL) (hwe : PGen we)
    (jM' : M'.ι) (jL' : L'.ι) :
    ∃ s : Γ(Ge', (M'.pull pG').U (fun _ => jM') ⊓ (L'.pull fG').U (fun _ => jL'))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jL : L.ι), Φ (pG' (r z)) ∈ M.U jM →
        pG' (r z) ∈ M'.U jM' → Ψ (fG' (r z)) ∈ L.U jL → fG' (r z) ∈ L'.U jL' →
        gm r z _ s = germ pG' fG' h w wL we r z jM jM' jL jL' := by sorry
