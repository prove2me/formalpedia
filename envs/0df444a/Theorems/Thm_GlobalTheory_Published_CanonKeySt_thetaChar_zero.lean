-- Prove2me | Theorems.Thm_GlobalTheory_Published_CanonKeySt_thetaChar_zero
-- name    : GlobalTheory.Published.CanonKeySt.thetaChar_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:22:43.509346+00:00
-- url     : https://prove2.me/theorems/4e6dd307-6735-420d-895d-d4678bcf7648
-- title:
--   Canon Key St: theta Char zero
-- statement:
--   The Canon Key St construction uses the theta Char zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/ThetaCharacteristics/ThetaCharZero.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/ThetaCharacteristics/ThetaCharZero.lean#L36-L40

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

theorem GlobalTheory.Published.CanonKeySt.thetaChar_zero {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    thetaChar τ 0 0 z = ∑' n : Fin g → ℤ,
      Complex.exp (Real.pi * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec fun i => (n i : ℂ)) +
        2 * Real.pi * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ z)) := by sorry
