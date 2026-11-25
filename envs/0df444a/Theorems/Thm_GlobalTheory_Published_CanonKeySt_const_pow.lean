-- Prove2me | Theorems.Thm_GlobalTheory_Published_CanonKeySt_const_pow
-- name    : GlobalTheory.Published.CanonKeySt.const_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:16:33.253802+00:00
-- url     : https://prove2.me/theorems/65306914-6e92-4ddc-86bf-1caaed31855b
-- title:
--   Canon Key St: const pow
-- statement:
--   The Canon Key St construction uses the const pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/ThetaCharacteristics/ThetaCharZero.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/ThetaCharacteristics/ThetaCharZero.lean#L42-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_ThetaCharacteristics_ThetaCharZero
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
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.CanonKeySt

theorem GlobalTheory.Published.CanonKeySt.const_pow (g : ℕ) :
    ((2 * Real.pi * Complex.I : ℂ) ^ g) ^ 4 = (2 * Real.pi : ℂ) ^ (4 * g) := by sorry
