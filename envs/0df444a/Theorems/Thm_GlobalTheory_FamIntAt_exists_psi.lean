-- Prove2me | Theorems.Thm_GlobalTheory_FamIntAt_exists_psi
-- name    : GlobalTheory.FamIntAt.exists_psi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:55.916278+00:00
-- url     : https://prove2.me/theorems/a2b88fc1-2cbc-4333-85fc-1f9f669c834c
-- title:
--   Fam Int At: exists psi
-- statement:
--   The Fam Int At construction uses the exists psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IntegralFamilyPrescribedTermUnitAtPrime.lean#L215-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IntegralFamilyPrescribedTermUnitAtPrime.lean#L215-L250

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

theorem GlobalTheory.FamIntAt.exists_psi {I : Ideal R} (D : DegData R I) (χ : D.toPre.X) :
    ∃ Ψ : LB.Sec (LB.LinComb D.toPre.P.L (Y := Spec (CommRingCat.of R)) (K := PUnit) (fun _ => (D.toPre.c χ).left)
      (fun _ => -1)), ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) (FractionRing R)) (z : T.left) (J),
        Good D.toPre.P.L z J → sval Ψ ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z J =
          (val (D.toPre.psi χ) (σ.left ≫ jFK (R := R) (FractionRing R)) z J).val := by sorry
