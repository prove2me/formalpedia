-- Prove2me | Theorems.Thm_GlobalTheory_ComplexPoints_iSup_eq_top_of_complexPoints
-- name    : GlobalTheory.ComplexPoints.iSup_eq_top_of_complexPoints
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:32.580844+00:00
-- url     : https://prove2.me/theorems/e5dac314-01b0-4170-939d-e9219acc18d7
-- title:
--   Complex Points: i Sup eq top of complex Points
-- statement:
--   The Complex Points construction uses the i Sup eq top of complex Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L265-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L265-L272

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
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {X Y : Scheme.{0}}

theorem GlobalTheory.ComplexPoints.iSup_eq_top_of_complexPoints (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    {I : Type*} (U : I → X.Opens) (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ i, ⊤ ≤ x ⁻¹ᵁ U i) :
    ⨆ i, U i = ⊤ := by sorry
