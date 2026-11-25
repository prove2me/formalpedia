-- Prove2me | Theorems.Thm_GlobalTheory_GrpDescent_grpObj_descends_faithfullyFlat
-- name    : GlobalTheory.GrpDescent.grpObj_descends_faithfullyFlat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:24.17627+00:00
-- url     : https://prove2.me/theorems/d3e7fb54-a731-5361-99da-9ab1d8b52dde
-- title:
--   Grp Descent: grp Obj descends faithfully Flat
-- statement:
--   The Grp Descent construction uses the grp Obj descends faithfully Flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/GrpObjDescendsFaithfullyFlat.lean#L137-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/GrpObjDescendsFaithfullyFlat.lean#L137-L141

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

theorem GlobalTheory.GrpDescent.grpObj_descends_faithfullyFlat : ∀ (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] [Module.FaithfullyFlat R₀ R] (A : Over (Sp R)) [GrpObj A] (A₀ : Over (Sp R₀)) [Flat A₀.hom] [IsSeparated A₀.hom] [QuasiCompact A₀.hom] (π : A.left ⟶ A₀.left) (e₀ : 𝟙_ (Over (Sp R₀)) ⟶ A₀) (m₀ : A₀ ⊗ A₀ ⟶ A₀) (i₀ : A₀ ⟶ A₀) (π₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left), IsPullback π A.hom A₀.hom (spMap (algebraMap R₀ R)) → π₂ ≫ (fst A₀ A₀).left = (fst A A).left ≫ π → π₂ ≫ (snd A₀ A₀).left = (snd A A).left ≫ π → η[A].left ≫ π = spMap (algebraMap R₀ R) ≫ e₀.left → μ[A].left ≫ π = π₂ ≫ m₀.left → (GrpObj.inv : A ⟶ A).left ≫ π = π ≫ i₀.left → ∃ _ : GrpObj A₀, IsGrpPullback A A₀ (spMap (algebraMap R₀ R)) π := by sorry
