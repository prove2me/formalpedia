-- Prove2me | Theorems.Thm_GlobalTheory_GrpDescent_grpObj_descends
-- name    : GlobalTheory.GrpDescent.grpObj_descends
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:57:49.247207+00:00
-- url     : https://prove2.me/theorems/c629fa5e-0b80-4475-b9c9-f9d2aab003ac
-- title:
--   Grp Descent: grp Obj descends
-- statement:
--   The Grp Descent construction uses the grp Obj descends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/GrpObjDescendsFaithfullyFlat.lean#L22-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/GrpObjDescendsFaithfullyFlat.lean#L22-L135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_GrpObjDescendsFaithfullyFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.GrpDescent
variable {S S₀ : Scheme.{0}}

theorem GlobalTheory.GrpDescent.grpObj_descends (f : S ⟶ S₀) [Flat f] [Surjective f] (A : Over S) [GrpObj A] (A₀ : Over S₀)
    (π : A.left ⟶ A₀.left) (e₀ : 𝟙_ (Over S₀) ⟶ A₀) (m₀ : A₀ ⊗ A₀ ⟶ A₀) (i₀ : A₀ ⟶ A₀)
    (π₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left) (hπ : IsPullback π A.hom A₀.hom f)
    (h1 : π₂ ≫ (fst A₀ A₀).left = (fst A A).left ≫ π) (h2 : π₂ ≫ (snd A₀ A₀).left = (snd A A).left ≫ π)
    (he : η[A].left ≫ π = f ≫ e₀.left) (hm : μ[A].left ≫ π = π₂ ≫ m₀.left)
    (hi : (GrpObj.inv : A ⟶ A).left ≫ π = π ≫ i₀.left) :
    ∃ _ : GrpObj A₀, IsGrpPullback A A₀ f π := by sorry
