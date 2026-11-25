-- Prove2me | Theorems.Thm_GlobalTheory_ClosedLimit_descends_of_isAffine
-- name    : GlobalTheory.ClosedLimit.descends_of_isAffine
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:48:30.245842+00:00
-- url     : https://prove2.me/theorems/f07a7902-6188-4998-bf06-f1891c244843
-- title:
--   Closed Limit: descends of is Affine
-- statement:
--   The Closed Limit construction uses the descends of is Affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsClosedImmersionDescendsToSubring.lean#L172-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsClosedImmersionDescendsToSubring.lean#L172-L200

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsClosedImmersionDescendsToSubring
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
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.ClosedLimit
universe u
open GlobalTheory.Spread

theorem GlobalTheory.ClosedLimit.descends_of_isAffine (S : Type) [CommRing S] (R₀ : Subring S) (X₀ Y₀ X Y : Scheme.{0})
    (g₀ : X₀ ⟶ Y₀) (q : Y₀ ⟶ Sp R₀) [IsAffine Y₀] [QuasiCompact g₀] [QuasiSeparated g₀]
    [LocallyOfFiniteType g₀] (g : X ⟶ Y) (πX : X ⟶ X₀) (πY : Y ⟶ Y₀) (p : Y ⟶ Sp S)
    (hY : IsPullback πY p q (spMap R₀.subtype)) (hX : IsPullback πX g g₀ πY)
    (hg : IsClosedImmersion g) :
    ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ →
      ∀ (X₁ Y₁ : Scheme.{0}) (g₁ : X₁ ⟶ Y₁) (πX₁ : X₁ ⟶ X₀) (πY₁ : Y₁ ⟶ Y₀) (p₁ : Y₁ ⟶ Sp R₁),
        πY₁ ≫ q = p₁ ≫ spMap (Subring.inclusion h) → IsPullback πX₁ g₁ g₀ πY₁ →
          IsClosedImmersion g₁ := by sorry
