-- Prove2me | Theorems.Thm_GlobalTheory_units_modSq_finite_of_fields
-- name    : GlobalTheory.units_modSq_finite_of_fields
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:31:18.515189+00:00
-- url     : https://prove2.me/theorems/a475183f-94d9-4491-b501-4eaf398e2305
-- title:
--   Global Theory: units mod Sq finite of fields
-- statement:
--   The Global Theory construction uses the units mod Sq finite of fields property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitsModSqFiniteOfFields.lean#L31-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitsModSqFiniteOfFields.lean#L31-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitsModSqFiniteOfFields
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.units_modSq_finite_of_fields : ∀ (k : Type) [Field k] [CharZero k],
    (∀ (L : Type) [Field L] [Algebra k L] [FiniteDimensional k L],
      Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range)) →
    ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A],
      Finite (Aˣ ⧸ (powMonoidHom 2 : Aˣ →* Aˣ).range) := by sorry
