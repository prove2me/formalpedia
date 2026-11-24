-- Prove2me | Theorems.Thm_GlobalTheory_exists_primitive_idempotent_map_eq_one
-- name    : GlobalTheory.exists_primitive_idempotent_map_eq_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:44.199283+00:00
-- url     : https://prove2.me/theorems/51392160-5b29-46a6-aa7a-f0f1f7d3302b
-- title:
--   Global Theory: exists primitive idempotent map eq one
-- statement:
--   The Global Theory construction uses the exists primitive idempotent map eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPrimitiveIdempotentMapEqOne.lean#L8-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPrimitiveIdempotentMapEqOne.lean#L8-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPrimitiveIdempotentMapEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_primitive_idempotent_map_eq_one {A R : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing R] [IsDomain R] (φ : A →+* R) :
    ∃ e : A, e * e = e ∧ e ≠ 0 ∧ (∀ f : A, f * f = f → f * e = f → f = 0 ∨ f = e) ∧ φ e = 1 := by sorry
