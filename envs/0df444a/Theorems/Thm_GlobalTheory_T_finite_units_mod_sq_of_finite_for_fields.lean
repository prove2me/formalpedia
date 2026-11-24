-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_units_mod_sq_of_finite_for_fields
-- name    : GlobalTheory.T.finite_units_mod_sq_of_finite_for_fields
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:39:42.080915+00:00
-- url     : https://prove2.me/theorems/e6c09bf2-d9f9-41fe-a45f-41920204e9b5
-- title:
--   T: finite units mod sq of finite for fields
-- statement:
--   The T construction uses the finite units mod sq of finite for fields property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitsModSqFiniteOfFieldsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitsModSqFiniteOfFieldsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitsModSqFiniteOfFields
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitsModSqFiniteOfFieldsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_units_mod_sq_of_finite_for_fields : ∀ (k : Type) [Field k] [CharZero k], (∀ (L : Type) [Field L] [Algebra k L] [FiniteDimensional k L], Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range)) → ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], Finite (Aˣ ⧸ (powMonoidHom 2 : Aˣ →* Aˣ).range) := by sorry
