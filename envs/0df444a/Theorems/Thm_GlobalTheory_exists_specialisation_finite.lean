-- Prove2me | Theorems.Thm_GlobalTheory_exists_specialisation_finite
-- name    : GlobalTheory.exists_specialisation_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:13:04.744565+00:00
-- url     : https://prove2.me/theorems/b7d1e7d4-c751-4c21-bdda-073f7a07430d
-- title:
--   Global Theory: exists specialisation finite
-- statement:
--   The Global Theory construction uses the exists specialisation finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SpecialisationNumberFieldAndCountableValues.lean#L87-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SpecialisationNumberFieldAndCountableValues.lean#L87-L122

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

theorem GlobalTheory.exists_specialisation_finite {k L : Type*} [Field k] [Field L]
    [Algebra k L] [IsAlgClosed L] (R : Subalgebra k L) (hR : R.FG) (r : R) (hr : r ≠ 0) :
    ∃ (K₁ : IntermediateField k L) (ρ : R →ₐ[k] K₁), FiniteDimensional k K₁ ∧ ρ r ≠ 0 ∧
      ∀ c : R, IsAlgebraic k c → (ρ c : L) = c := by sorry
