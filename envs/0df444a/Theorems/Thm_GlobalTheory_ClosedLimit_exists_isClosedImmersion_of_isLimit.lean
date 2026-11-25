-- Prove2me | Theorems.Thm_GlobalTheory_ClosedLimit_exists_isClosedImmersion_of_isLimit
-- name    : GlobalTheory.ClosedLimit.exists_isClosedImmersion_of_isLimit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:01:33.764703+00:00
-- url     : https://prove2.me/theorems/d60397af-3f96-5be4-9d4a-6c952dd2b279
-- title:
--   Closed Limit: exists is Closed Immersion of is Limit
-- statement:
--   The Closed Limit construction uses the exists is Closed Immersion of is Limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsClosedImmersionDescendsToSubring.lean#L36-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsClosedImmersionDescendsToSubring.lean#L36-L103

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

theorem GlobalTheory.ClosedLimit.exists_isClosedImmersion_of_isLimit {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D E : I ⥤ Scheme.{u}) (α : D ⟶ E) (c : Cone D) (d : Cone E) (hc : IsLimit c) (hd : IsLimit d)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] [∀ i, IsAffine (E.obj i)]
    [∀ i, LocallyOfFiniteType (α.app i)]
    (hα : ∀ {i j} (f : i ⟶ j), IsPullback (D.map f) (α.app i) (α.app j) (E.map f))
    (g : c.pt ⟶ d.pt) [IsClosedImmersion g] (hg : ∀ i, g ≫ d.π.app i = c.π.app i ≫ α.app i) :
    ∃ i, IsClosedImmersion (α.app i) := by sorry
