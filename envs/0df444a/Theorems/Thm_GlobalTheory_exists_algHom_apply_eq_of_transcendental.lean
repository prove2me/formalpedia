-- Prove2me | Theorems.Thm_GlobalTheory_exists_algHom_apply_eq_of_transcendental
-- name    : GlobalTheory.exists_algHom_apply_eq_of_transcendental
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:46:12.456063+00:00
-- url     : https://prove2.me/theorems/fd2b75e2-7c9c-492f-95be-a4d07555f5eb
-- title:
--   Global Theory: exists alg Hom apply eq of transcendental
-- statement:
--   The Global Theory construction uses the exists alg Hom apply eq of transcendental property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SpecialisationNumberFieldAndCountableValues.lean#L124-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SpecialisationNumberFieldAndCountableValues.lean#L124-L143

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

theorem GlobalTheory.exists_algHom_apply_eq_of_transcendental {k L : Type*} [Field k] [Field L] [Algebra k L]
    [IsAlgClosed L] (R : Subalgebra k L) (hR : R.FG) (c : R) (hc : Transcendental k (c : L))
    (t : L) (ht : Transcendental k t) : ∃ ρ : R →ₐ[k] L, ρ c = t := by sorry
