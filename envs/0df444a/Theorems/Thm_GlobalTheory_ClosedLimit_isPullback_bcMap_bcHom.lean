-- Prove2me | Theorems.Thm_GlobalTheory_ClosedLimit_isPullback_bcMap_bcHom
-- name    : GlobalTheory.ClosedLimit.isPullback_bcMap_bcHom
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:47:25.981873+00:00
-- url     : https://prove2.me/theorems/62b23de4-6fcd-4b04-89ba-7f4211929cc1
-- title:
--   Closed Limit: is Pullback bc Map bc Hom
-- statement:
--   The Closed Limit construction uses the is Pullback bc Map bc Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsClosedImmersionDescendsToSubring.lean#L129-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsClosedImmersionDescendsToSubring.lean#L129-L138

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
variable {k : Type} [CommRing k] {X₀ Y₀ : Scheme.{0}} (g₀ : X₀ ⟶ Y₀) (q : Y₀ ⟶ Sp k)

theorem GlobalTheory.ClosedLimit.isPullback_bcMap_bcHom {R A : Type} [CommRing R] [CommRing A] [Algebra k R] [Algebra k A]
    (f : R →ₐ[k] A) :
    IsPullback (bcMap (g₀ ≫ q) f) (bcHom g₀ q _) (bcHom g₀ q _) (bcMap q f) := by sorry
