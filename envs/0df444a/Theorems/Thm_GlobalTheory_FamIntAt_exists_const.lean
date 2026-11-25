-- Prove2me | Theorems.Thm_GlobalTheory_FamIntAt_exists_const
-- name    : GlobalTheory.FamIntAt.exists_const
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:20:21.586694+00:00
-- url     : https://prove2.me/theorems/d9671483-73b9-426d-b4e8-febf5ba5365f
-- title:
--   Fam Int At: exists const
-- statement:
--   The Fam Int At construction uses the exists const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IntegralFamilyPrescribedTermUnitAtPrime.lean#L309-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IntegralFamilyPrescribedTermUnitAtPrime.lean#L309-L357

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_exists_const

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
open SectionScalarValuation

theorem GlobalTheory.FamIntAt.exists_const {I : Ideal R} (D : DegData R I) (k : ℕ) (ρ mu : D.toPre.X) (r : R)
    (Φ : LB.Sec (LB.LinComb D.toPre.P.L (Y := Spec (CommRingCat.of R)) (K := PUnit) (fun _ => (D.toPre.c ρ).left)
      (fun _ => - -1)))
    (hΦ : ∀ (T : Scheme.{0}) (τ : T ⟶ (TK R).left) (z : T) (J), Good D.toPre.P.L z J →
      sval Φ (τ ≫ jK R) z J = gs (τ ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) *
        ((val (D.toPre.psi ρ) τ z J)⁻¹).val) :
    ∃ (Ix : Type) (_ : Fintype Ix) (φV : Ix → (Spec (CommRingCat.of R) ⟶ D.toPre.P.A.left)) (εV : Ix → ℤ)
      (w : LB.Sec (LB.LinComb D.toPre.P.L φV εV)),
      (∀ (U : Type) [CommGroup U] (h : (D.toPre.P.A.left ⟶ D.toPre.P.A.left) → U),
        ∏ i, h (D.toPre.P.A.hom ≫ φV i) ^ εV i =
          (h (cQ D.toPre D.toPre.P.A ρ * cQ D.toPre D.toPre.P.A mu).left)⁻¹ * h (cQ D.toPre D.toPre.P.A ρ).left *
            h (cQ D.toPre D.toPre.P.A mu).left * (h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left)⁻¹ *
            (h (cQ D.toPre D.toPre.P.A mu).left ^ (k + 1))⁻¹ * h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left ^ (k + 1)) ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) (FractionRing R)) (z : T.left) (J),
        Good D.toPre.P.L z J → sval w ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z J =
          gs ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) *
            (val (DegPre.famMult D.toPre (FractionRing R) (k + 1) mu ρ) σ.left z J).val := by sorry
