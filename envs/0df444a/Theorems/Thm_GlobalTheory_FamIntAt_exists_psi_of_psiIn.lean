-- Prove2me | Theorems.Thm_GlobalTheory_FamIntAt_exists_psi_of_psiIn
-- name    : GlobalTheory.FamIntAt.exists_psi_of_psiIn
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:20:14.925158+00:00
-- url     : https://prove2.me/theorems/83e14c5d-bad6-44c3-baee-397103922d8e
-- title:
--   Fam Int At: exists psi of psi In
-- statement:
--   The Fam Int At construction uses the exists psi of psi In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IntegralFamilyPrescribedTermUnitAtPrime.lean#L91-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IntegralFamilyPrescribedTermUnitAtPrime.lean#L91-L110

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

theorem GlobalTheory.FamIntAt.exists_psi_of_psiIn {D : DegPre R} {χ : D.X} {I : Ideal R} (h : D.PsiIn χ I) :
    ∃ Ψ : LB.Sec (LB.LinComb D.P.L (Y := Spec (CommRingCat.of R)) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)),
      ∀ (T : Scheme.{0}) (r : T ⟶ (TK R).left) (z : T) (J), Good D.P.L z J →
        sval Ψ (r ≫ jK R) z J = (val (D.psi χ) r z J).val := by sorry
