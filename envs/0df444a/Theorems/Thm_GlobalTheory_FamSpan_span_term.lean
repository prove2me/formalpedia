-- Prove2me | Theorems.Thm_GlobalTheory_FamSpan_span_term
-- name    : GlobalTheory.FamSpan.span_term
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:29:05.887318+00:00
-- url     : https://prove2.me/theorems/b6b13550-1710-4067-9c8e-5615e92bd616
-- title:
--   Fam Span: span term
-- statement:
--   The Fam Span construction uses the span term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsIntegralFamiliesSpanPullDegeneration.lean#L238-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsIntegralFamiliesSpanPullDegeneration.lean#L238-L286

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsRepresentativesModNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsBasisOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FamEqOnClassOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIntegralFamiliesSpanPullDegeneration
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamSpan
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem GlobalTheory.FamSpan.span_term (hD : IsPullDeg φ D D') (k : ℕ) (x : D'.X) {m : ℕ} (b g : Fin m → D.SecB k (hD.xe x))
    (hb : IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap R' (FractionRing R')).comp φ))))
      (A := D.P.A) _ (fun i => DVR.pullSec D.P.L (D.famφB (hD.xe x)) (DegPre.famε k) (b i)
        (snd (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap R' (FractionRing R')).comp φ)))) D.P.A).left))
    (r : Fin m → R) (hr : ∀ i, algebraMap R' (FractionRing R') (φ (r i)) ≠ 0)
    (hg : ∀ i j, (g i).f j = resTop _ (scal D.P.A.hom (r i)) * (b i).f j) (g' : Fin m → D'.SecB k x)
    (hg' : ∀ i (y : (DegPre.BF D' (FractionRing R')).left) J J', Good D.P.L y J → Good D'.P.L y J' →
      sval (g i) ((𝟙 _ ≫ (DegPre.prB D' (FractionRing R')).left) ≫
        (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) y J =
      (fac hD.w (D'.famφB x) (DegPre.famε k) (𝟙 _ ≫ (DegPre.prB D' (FractionRing R')).left) y J J').val *
        sval (g' i) (𝟙 _ ≫ (DegPre.prB D' (FractionRing R')).left) y J')
    (G : Fin m → LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' (FractionRing R') x) (DegPre.famε k)))
    (hG : ∀ i, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') x) (DegPre.famε k) (G i) (D'.famφB x)
      (DegPre.famε k) (g' i) (DegPre.prB D' (FractionRing R')).left 1)
    (s : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' (FractionRing R') x) (DegPre.famε k))) :
    ∃ c : Fin m → FractionRing R', ∀ j, s.f j = ∑ i, resTop _ (DVR.gF D' (FractionRing R') (c i)) * (G i).f j := by sorry
