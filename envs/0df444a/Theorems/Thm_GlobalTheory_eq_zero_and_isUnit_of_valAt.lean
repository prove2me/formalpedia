-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_and_isUnit_of_valAt
-- name    : GlobalTheory.eq_zero_and_isUnit_of_valAt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:38.651032+00:00
-- url     : https://prove2.me/theorems/909a3126-29a2-4a45-9160-e5df8eea89d7
-- title:
--   Global Theory: eq zero and is Unit of val At
-- statement:
--   The Global Theory construction uses the eq zero and is Unit of val At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L292-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SurjectiveOfComplexPointsLiftOfUniversallyClosed.lean#L292-L298

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
open GlobalTheory

theorem GlobalTheory.eq_zero_and_isUnit_of_valAt :
    ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X] (U : X.Opens)
      (f : Γ(X, U)),
      ((∀ (x : Sp ℂ ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U h f = 0) → f = 0) ∧
      ((∀ (x : Sp ℂ ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U h f ≠ 0) → IsUnit f) := by sorry
