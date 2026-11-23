-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_translate_comp
-- name    : GlobalTheory.KeyKa.EtBaseChange.translate_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:16.617263+00:00
-- url     : https://prove2.me/theorems/aeb35058-7bb7-4b08-a16f-b64fec497039
-- title:
--   Et Base Change: translate comp
-- statement:
--   The Et Base Change construction uses the translate comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusVia.lean#L116-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusVia.lean#L116-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
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
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.EtBaseChange
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem GlobalTheory.KeyKa.EtBaseChange.translate_comp {R' : Type} [CommRing R'] {G' : Over (Sp R')} [GrpObj G'] {f : R →+* R'}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) φ) (F : DualNumber R →+* DualNumber R')
    (h₁ : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a))
    (z : 𝟙_ (Over (Sp R)) ⟶ G) (z' : 𝟙_ (Over (Sp R')) ⟶ G') (hz : z'.left ≫ φ = spMap f ≫ z.left)
    (v : epsR R ⟶ G) (v' : epsR R' ⟶ G') (hv : v'.left ≫ φ = spMap F ≫ v.left) :
    ((toUnit (epsR R') ≫ z') * v').left ≫ φ = spMap F ≫ ((toUnit (epsR R) ≫ z) * v).left := by sorry
