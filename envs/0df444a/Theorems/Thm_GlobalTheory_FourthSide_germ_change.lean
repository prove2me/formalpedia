-- Prove2me | Theorems.Thm_GlobalTheory_FourthSide_germ_change
-- name    : GlobalTheory.FourthSide.germ_change
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:11:35.550846+00:00
-- url     : https://prove2.me/theorems/67eb7958-cb53-41f6-9911-437f2674ebbc
-- title:
--   Fourth Side: germ change
-- statement:
--   The Fourth Side construction uses the germ change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFourthSide.lean#L30-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFourthSide.lean#L30-L61

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

theorem GlobalTheory.FourthSide.germ_change (e₁ : pG' ≫ Φ = h ≫ pG) (e₂ : h ≫ fG = fG' ≫ Ψ) {w : LB.Iso M' (M.pull Φ)}
    {wL : LB.Iso L' (L.pull Ψ)} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : PGen w) (hwL : PGen wL) (hwe : PGen we)
    {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM kM : M.ι) (jM' kM' : M'.ι) (jL kL : L.ι) (jL' kL' : L'.ι)
    (a₁ : Φ (pG' (r z)) ∈ M.U jM) (a₂ : pG' (r z) ∈ M'.U jM') (a₃ : Ψ (fG' (r z)) ∈ L.U jL)
    (a₄ : fG' (r z) ∈ L'.U jL') (b₁ : Φ (pG' (r z)) ∈ M.U kM) (b₂ : pG' (r z) ∈ M'.U kM')
    (b₃ : Ψ (fG' (r z)) ∈ L.U kL) (b₄ : fG' (r z) ∈ L'.U kL') :
    germ pG' fG' h w wL we r z jM jM' jL jL' =
      gm (r ≫ pG') z _ (M'.g jM' kM') * (gm (r ≫ fG') z _ (L'.g jL' kL'))⁻¹ *
        germ pG' fG' h w wL we r z kM kM' kL kL' := by sorry
