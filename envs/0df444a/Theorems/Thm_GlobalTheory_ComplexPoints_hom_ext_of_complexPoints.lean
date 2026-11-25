-- Prove2me | Theorems.Thm_GlobalTheory_ComplexPoints_hom_ext_of_complexPoints
-- name    : GlobalTheory.ComplexPoints.hom_ext_of_complexPoints
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:52.111798+00:00
-- url     : https://prove2.me/theorems/fe8c876a-79e4-48e8-a3c2-b91b80e6a75e
-- title:
--   Complex Points: hom ext of complex Points
-- statement:
--   The Complex Points construction uses the hom ext of complex Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L231-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L231-L234

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

theorem GlobalTheory.ComplexPoints.hom_ext_of_complexPoints (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    (q : Y ⟶ Sp ℂ) [IsSeparated q] {f g : X ⟶ Y} (hf : f ≫ q = p) (hg : g ≫ q = p)
    (h : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → x ≫ f = x ≫ g) : f = g := by sorry
