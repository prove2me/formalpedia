-- Prove2me | Theorems.Thm_GlobalTheory_FamGen_comb_term
-- name    : GlobalTheory.FamGen.comb_term
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:50:39.688934+00:00
-- url     : https://prove2.me/theorems/9dfa4237-1b9e-53fc-a5e6-c92ecd4aa53d
-- title:
--   Fam Gen: comb term
-- statement:
--   The Fam Gen construction uses the comb term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsIntegralFamiliesSpanGenerateValuationRings.lean#L43-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsIntegralFamiliesSpanGenerateValuationRings.lean#L43-L89

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
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsRepresentativesModNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsBasisOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FamEqOnClassOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntegralDegenerationFamilyBaseChangeExtensionFie
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIntegralFamiliesSpanPullDegeneration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIntegralFamiliesSpanGenerateValuationRings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamGen
open GlobalTheory.FamSpan GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.FamGen.comb_term {S : Type} [CommRing S] (σ : R →+* S) (ιF : S →+* F)
    (ρ : TF (R := R) F ⟶ Over.mk (specOf σ)) (hρ : ρ.left = specOf ιF) (k : ℕ) (α : D.X) {m : ℕ}
    (b g : Fin m → D.SecB k α)
    (hb : IsSecBasis (T := Over.mk (specOf σ)) (A := D.P.A) _ (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k)
      (b i) (snd (Over.mk (specOf σ)) D.P.A).left))
    (r : Fin m → R) (hr : ∀ i, IsUnit (σ (r i)))
    (hg : ∀ i j, (g i).f j = resTop _ (scal D.P.A.hom (r i)) * (b i).f j)
    (G : Fin m → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (hG : ∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (G i) (D.famφB α)
      (DegPre.famε k) (g i) (DegPre.prB D F).left 1)
    (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (sg : LB.Sec (LB.LinComb D.P.L (fun i => (snd (Over.mk (specOf σ)) D.P.A).left ≫ D.famφB α i) (DegPre.famε k)))
    (hsg : GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) s
      (fun i => (snd (Over.mk (specOf σ)) D.P.A).left ≫ D.famφB α i) (DegPre.famε k) sg (ρ ▷ D.P.A).left 1) :
    ∃ c : Fin m → S, ∀ j, s.f j = ∑ i, resTop _ (DVR.gF D F (ιF (c i))) * (G i).f j := by sorry
