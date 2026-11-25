-- Prove2me | Theorems.Thm_GlobalTheory_SimilUnit_IsVal_exists_unit
-- name    : GlobalTheory.SimilUnit.IsVal.exists_unit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:29:51.764984+00:00
-- url     : https://prove2.me/theorems/fe82c0ba-e26f-5e93-9d7d-0f04a7a39deb
-- title:
--   Is Val: exists unit
-- statement:
--   The Is Val construction uses the exists unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsNormalisingUnitSimilitudeOrigin.lean#L79-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsNormalisingUnitSimilitudeOrigin.lean#L79-L89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNormalisingUnitSimilitudeOrigin
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
open GlobalTheory GlobalTheory.SimilUnit
variable {X Y Y' : Scheme.{0}} (L : LB X)
variable {L} {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
  {v v' : ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ}

theorem GlobalTheory.SimilUnit.IsVal.exists_unit (hL : L.IsLB) (a : IsVal L F v)
    (h1 : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), F U h = 1) :
    ∃ u : Γ(Y, ⊤)ˣ, ∀ y J, Good L y J → (v y J).val = gs (𝟙 Y) y ⊤ u.val := by sorry
