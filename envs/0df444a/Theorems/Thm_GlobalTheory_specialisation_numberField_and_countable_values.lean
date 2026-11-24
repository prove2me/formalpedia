-- Prove2me | Theorems.Thm_GlobalTheory_specialisation_numberField_and_countable_values
-- name    : GlobalTheory.specialisation_numberField_and_countable_values
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:59.446794+00:00
-- url     : https://prove2.me/theorems/bebfc21f-f59a-4d33-a45e-8691ca3726de
-- title:
--   Global Theory: specialisation number Field and countable values
-- statement:
--   The Global Theory construction uses the specialisation number Field and countable values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SpecialisationNumberFieldAndCountableValues.lean#L145-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SpecialisationNumberFieldAndCountableValues.lean#L145-L182

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.specialisation_numberField_and_countable_values :
    ∀ (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (R : Subalgebra k ℂ), R.FG →
    ∀ (c r : R), r ≠ 0 →
    (∃ (K₁ : IntermediateField k ℂ) (ρ : R →ₐ[k] K₁), FiniteDimensional k K₁ ∧ ρ r ≠ 0 ∧
      (IsAlgebraic k c → (ρ c : ℂ) = c)) ∧
    (∀ S : Set ℂ, S.Countable → (∀ ρ : R →ₐ[k] ℂ, ρ c ∈ S) → IsAlgebraic k c) := by sorry
