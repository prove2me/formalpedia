-- Prove2me | Theorems.Thm_GlobalTheory_FamIntAt_local_inv
-- name    : GlobalTheory.FamIntAt.local_inv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:20:36.205202+00:00
-- url     : https://prove2.me/theorems/637a7caf-57db-4565-8a0d-09105f18491a
-- title:
--   Fam Int At: local inv
-- statement:
--   The Fam Int At construction uses the local inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IntegralFamilyPrescribedTermUnitAtPrime.lean#L112-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IntegralFamilyPrescribedTermUnitAtPrime.lean#L112-L163

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FamIntAt
variable {R : Type} [CommRing R] [IsDomain R]

theorem GlobalTheory.FamIntAt.local_inv {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens} (ψ : PsiOn D W) (ρ : D.X)
    (g : Γ(Spec (CommRingCat.of R), ⊤)) (hgW : (Spec (CommRingCat.of R)).basicOpen g ≤ W)
    (hg : jK R (genPt R) ∈ (Spec (CommRingCat.of R)).basicOpen g) (q : Spec (CommRingCat.of R)) :
    ∃ (j : D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens) (n : ℕ) (a : Γ(Spec (CommRingCat.of R), V)), q ∈ V ∧
      V ≤ (D.c ρ).left ⁻¹ᵁ D.P.L.U j ∧ gs (jK R) (genPt R) V a = gs (jK R) (genPt R) ⊤ g ^ n *
        ((gm (𝟙 _) (genPt R) (LB.wchart D.P.L (fun _ : PUnit => D.xK ρ) (fun _ => j))
          ((D.psi ρ).s (fun _ => j)))⁻¹).val := by sorry
