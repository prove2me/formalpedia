-- Prove2me | Theorems.Thm_GlobalTheory_nsmul_surj_of_card_torsion
-- name    : GlobalTheory.nsmul_surj_of_card_torsion
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:56.842797+00:00
-- url     : https://prove2.me/theorems/7bd635e6-579b-482c-924a-3c4ced621c9e
-- title:
--   Global Theory: nsmul surj of card torsion
-- statement:
--   The Global Theory construction uses the nsmul surj of card torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionLiftNumberFieldModule.lean#L50-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionLiftNumberFieldModule.lean#L50-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionLiftNumberFieldModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory

theorem GlobalTheory.nsmul_surj_of_card_torsion :
    ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    (∀ j : ℕ, Nat.card {x : M // (N ^ j) • x = 0} = (N ^ j) ^ (2 * Module.finrank ℚ F)) →
    ∀ j : ℕ, ∀ y : M, (N ^ j) • y = 0 → ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y := by sorry
