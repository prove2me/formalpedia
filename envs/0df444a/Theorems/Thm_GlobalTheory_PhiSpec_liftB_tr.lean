-- Prove2me | Theorems.Thm_GlobalTheory_PhiSpec_liftB_tr
-- name    : GlobalTheory.PhiSpec.liftB_tr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:56:34.367401+00:00
-- url     : https://prove2.me/theorems/c1da8db5-0a70-4cd7-b61b-9f18b5ef777f
-- title:
--   Phi Spec: lift B tr
-- statement:
--   The Phi Spec construction uses the lift B tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiSpecialises.lean#L256-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiSpecialises.lean#L256-L264

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
import Theorems.Thm_GlobalTheory_PhiPull_liftB_tr

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

theorem GlobalTheory.PhiSpec.liftB_tr (ρ : T' ⟶ DegPre.BF D' F) {b : T ⟶ D.P.A} {b' : TF (R := R') F ⟶ D'.P.A}
    (hb : b'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ b.left) :
    liftB hT hΘ₁ ρ ≫ trT D b = liftB hT hΘ₁ (ρ ≫ DegPre.trPt D' F b') := by sorry
