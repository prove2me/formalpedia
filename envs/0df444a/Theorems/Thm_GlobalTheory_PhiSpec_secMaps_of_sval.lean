-- Prove2me | Theorems.Thm_GlobalTheory_PhiSpec_secMaps_of_sval
-- name    : GlobalTheory.PhiSpec.secMaps_of_sval
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:46:19.951896+00:00
-- url     : https://prove2.me/theorems/fcc5eb71-af31-4db6-864e-f8213e3e23aa
-- title:
--   Phi Spec: sec Maps of sval
-- statement:
--   The Phi Spec construction uses the sec Maps of sval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiSpecialises.lean#L323-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiSpecialises.lean#L323-L342

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiSpecialises
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
open GlobalTheory.PhiSpec
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {T : Over (Spec (CommRingCat.of R))} {F : Type} [Field F] [Algebra (FractionRing R') F]
  (hD : IsPullDeg φ D D') {h : (TF (R := R') F).left ⟶ T.left} (hT : (TF (R := R') F).hom ≫ spMap φ = h ≫ T.hom)
  {Θ : (DegPre.BF D' F).left ⟶ (T ⊗ D.P.A).left}
  (hΘ₁ : Θ ≫ (fst T D.P.A).left = (fst (TF (R := R') F) D'.P.A).left ≫ h)
  (hΘ₂ : Θ ≫ (snd T D.P.A).left = (DegPre.prB D' F).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
  {T' : Over (Spec (CommRingCat.of R'))}
include hΘ₂

theorem GlobalTheory.PhiSpec.secMaps_of_sval {k : ℕ} (x : D'.X) (s : SecT D T k (hD.xe x))
    (s' : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F x) (DegPre.famε k)))
    (H : ∀ (T' : Over (Spec (CommRingCat.of R'))) (ρ : T' ⟶ DegPre.BF D' F) (z : T'.left) (J J'),
      Good D.P.L z J → Good D'.P.L z J' → ∀ (Ω : (T' ⟶ D'.P.A) → (T'.left.presheaf.stalk z)ˣ),
      (Ω = fun x => gw hD.w x.left z (J (x.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' x.left)) →
      @Eq (T'.left.presheaf.stalk z) (sval s (liftB hT hΘ₁ ρ).left z J)
      ((Ω (ρ ≫ DegPre.prB D' F) ^ ((k : ℤ) - 1) * Ω (cP D' T' x * (ρ ≫ DegPre.prB D' F)) * (Ω (cP D' T' x))⁻¹ *
        Ω 1).val * sval s' ρ.left z J')) : SecMaps hD Θ x s s' := by sorry
