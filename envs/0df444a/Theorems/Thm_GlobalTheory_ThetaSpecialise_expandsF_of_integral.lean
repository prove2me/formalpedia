-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSpecialise_expandsF_of_integral
-- name    : GlobalTheory.ThetaSpecialise.expandsF_of_integral
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:48.236651+00:00
-- url     : https://prove2.me/theorems/768cfe48-e2d8-4a02-8585-f57de0cf3644
-- title:
--   Theta Specialise: expands F of integral
-- statement:
--   The Theta Specialise construction uses the expands F of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsFOfIntegral.lean#L194-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsFOfIntegral.lean#L194-L237

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMoveMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsFOfIntegral
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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.ThetaSpecialise.expandsF_of_integral {k : ℕ}
    {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))}
    {u : LB.Iso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R)))}
    (hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ A.A.left) (z : Z) (j : U.LG.L.ι) (i : A.L.ι),
      (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) (f z) ∈ U.LG.L.U j → f z ∈ A.L.U i →
      gw u f z j i = isoVal w (f ≫ U.gen.inv.left) z j i)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hE : ∀ e, U.ExpandsAt e k σ f) (s : Fam D.toPre F k)
    (hs : ∀ α y J, Good D.toPre.P.L y J →
      sval (s.s α) (𝟙 _) y J = sval (f α) (𝟙 _ ≫ (DegPre.prB D.toPre F).left) y J)
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)))
    (ht : PSec u (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))
      ((snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) t σ) :
    U.ExpandsF F k w t s := by sorry
