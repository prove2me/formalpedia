-- Prove2me | Theorems.Thm_GlobalTheory_PhiPull_sval_rel
-- name    : GlobalTheory.PhiPull.sval_rel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:49.413124+00:00
-- url     : https://prove2.me/theorems/9f81c5a7-e89e-4b4d-aac4-77e8433b04e7
-- title:
--   Phi Pull: sval rel
-- statement:
--   The Phi Pull construction uses the sval rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiRelTransport.lean#L157-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiRelTransport.lean#L157-L178

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
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
open GlobalTheory.PhiPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
variable {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
variable (hD : IsPullDeg φ D D') (hT : (TF (R := R') F).hom ≫ spMap φ = (TF (R := R) F).hom)
  {Θ : (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left}
  (hΘ₁ : Θ ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R') F) D'.P.A).left)
  (hΘ₂ : Θ ≫ (DegPre.prB D F).left = (DegPre.prB D' F).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
  {T' : Over (Spec (CommRingCat.of R'))}
include hΘ₂

theorem GlobalTheory.PhiPull.sval_rel {k : ℕ} (x : D'.X) (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F (hD.xe x)) (DegPre.famε k)))
    (s' : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F x) (DegPre.famε k)))
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι),
      (∀ κ, (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((DegPre.famφ D' F x) κ (r z)) ∈ D.P.L.U (p κ)) →
      (∀ κ, (DegPre.famφ D' F x) κ (r z) ∈ D'.P.L.U (q κ)) →
      gs (r ≫ Θ) z (LB.wchart D.P.L (DegPre.famφ D F (hD.xe x)) p) (s.f p) =
        (∏ κ, gw hD.w (r ≫ (DegPre.famφ D' F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val *
          gs r z (LB.wchart D'.P.L (DegPre.famφ D' F x) q) (s'.f q))
    (ρ : T' ⟶ DegPre.BF D' F) {z : T'.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (Ω : (T' ⟶ D'.P.A) → (T'.left.presheaf.stalk z)ˣ)
    (hΩ : Ω = fun x => gw hD.w x.left z (J (x.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' x.left)) :
    @Eq (T'.left.presheaf.stalk z) (sval s (liftB hT hΘ₁ ρ).left z J)
      ((Ω (ρ ≫ DegPre.prB D' F) ^ ((k : ℤ) - 1) * Ω (cP D' T' x * (ρ ≫ DegPre.prB D' F)) * (Ω (cP D' T' x))⁻¹ *
        Ω 1).val * sval s' ρ.left z J') := by sorry
