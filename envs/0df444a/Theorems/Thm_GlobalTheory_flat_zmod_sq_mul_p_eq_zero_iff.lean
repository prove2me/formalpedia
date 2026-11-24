-- Prove2me | Theorems.Thm_GlobalTheory_flat_zmod_sq_mul_p_eq_zero_iff
-- name    : GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:51:50.160806+00:00
-- url     : https://prove2.me/theorems/913e75e3-1901-48e8-9abd-3099dd5823b6
-- title:
--   Global Theory: flat zmod sq mul p eq zero iff
-- statement:
--   The Global Theory construction uses the flat zmod sq mul p eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlatModPSquaredTorsion.lean#L19-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlatModPSquaredTorsion.lean#L19-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlatModPSquaredTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory

theorem GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff : ∀ (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (φ : ZMod (p ^ 2) →+* B), φ.Flat → ∀ w : B, (p : B) * w = 0 ↔ ∃ v, w = p * v := by sorry
