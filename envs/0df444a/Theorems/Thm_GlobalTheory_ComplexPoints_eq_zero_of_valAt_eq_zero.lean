-- Prove2me | Theorems.Thm_GlobalTheory_ComplexPoints_eq_zero_of_valAt_eq_zero
-- name    : GlobalTheory.ComplexPoints.eq_zero_of_valAt_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:07:03.937343+00:00
-- url     : https://prove2.me/theorems/bd6ab91e-b984-4558-9733-d6fce3ea9ea2
-- title:
--   Complex Points: eq zero of val At eq zero
-- statement:
--   The Complex Points construction uses the eq zero of val At eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L157-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L157-L163

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

theorem GlobalTheory.ComplexPoints.eq_zero_of_valAt_eq_zero (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X] (U : X.Opens)
    (f : Γ(X, U))
    (h : ∀ (x : Sp ℂ ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U hx f = 0) : f = 0 := by sorry
