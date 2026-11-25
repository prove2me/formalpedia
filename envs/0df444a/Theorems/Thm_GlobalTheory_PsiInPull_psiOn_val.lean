-- Prove2me | Theorems.Thm_GlobalTheory_PsiInPull_psiOn_val
-- name    : GlobalTheory.PsiInPull.psiOn_val
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:56:51.8515+00:00
-- url     : https://prove2.me/theorems/89258964-61f3-43f0-bb50-c3725e9bc085
-- title:
--   Psi In Pull: psi On val
-- statement:
--   The Psi In Pull construction uses the psi On val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PsiInOfIsPullDeg.lean#L117-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PsiInOfIsPullDeg.lean#L117-L161

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PsiInPull

theorem GlobalTheory.PsiInPull.psiOn_val {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}
    (ψ : PsiOn D W) (χ : D.X) (p : D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens)
    (hVp : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U p)
    (h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (fun _ => p))
    (r : Γ(Spec (CommRingCat.of R), V))
    (hr : ((jK R).app V).hom r = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s (fun _ => p)).val)
    {Z : Scheme.{0}} (g : Z ⟶ W.toScheme) (z : Z) (hz : W.ι (g z) ∈ V) :
    (gm g z (LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c χ).left) (fun _ => p))
      ((ψ.psi χ).s (fun _ => p))).val = gs (g ≫ W.ι) z V r := by sorry
