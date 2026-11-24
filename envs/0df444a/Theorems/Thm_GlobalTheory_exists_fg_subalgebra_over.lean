-- Prove2me | Theorems.Thm_GlobalTheory_exists_fg_subalgebra_over
-- name    : GlobalTheory.exists_fg_subalgebra_over
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:29.34784+00:00
-- url     : https://prove2.me/theorems/2763a87e-4d9a-41bf-a326-7177669803e3
-- title:
--   Global Theory: exists fg subalgebra over
-- statement:
--   The Global Theory construction uses the exists fg subalgebra over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SpecialisationNumberFieldAndCountableValues.lean#L29-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SpecialisationNumberFieldAndCountableValues.lean#L29-L40

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

theorem GlobalTheory.exists_fg_subalgebra_over {k L : Type*} [Field k] [Field L] [Algebra k L]
    (F : IntermediateField k L) (R : Subalgebra k L) (hR : R.FG) (u : L) :
    ∃ A : Subalgebra F L, Algebra.FiniteType F A ∧ R ≤ A.restrictScalars k ∧ u ∈ A := by sorry
