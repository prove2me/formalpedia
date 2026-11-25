-- Prove2me | Theorems.Thm_GlobalTheory_ComplexPoints_opens_eq_top_of_complexPoints
-- name    : GlobalTheory.ComplexPoints.opens_eq_top_of_complexPoints
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:39.232863+00:00
-- url     : https://prove2.me/theorems/cc1398c0-d696-5eb1-aa8b-fab1dc02e34c
-- title:
--   Complex Points: opens eq top of complex Points
-- statement:
--   The Complex Points construction uses the opens eq top of complex Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L257-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L257-L259

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.ComplexPoints
variable {X Y : Scheme.{0}}

theorem GlobalTheory.ComplexPoints.opens_eq_top_of_complexPoints (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens)
    (h : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U) : U = ⊤ := by sorry
