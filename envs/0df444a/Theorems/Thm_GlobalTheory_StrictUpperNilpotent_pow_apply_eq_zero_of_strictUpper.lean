-- Prove2me | Theorems.Thm_GlobalTheory_StrictUpperNilpotent_pow_apply_eq_zero_of_strictUpper
-- name    : GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:22:35.311827+00:00
-- url     : https://prove2.me/theorems/971c8943-0797-4eec-ac96-3d2f08743859
-- title:
--   Strict Upper Nilpotent: pow apply eq zero of strict Upper
-- statement:
--   The Strict Upper Nilpotent construction uses the pow apply eq zero of strict Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PowApplyEqZeroOfStrictUpper.lean#L5-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PowApplyEqZeroOfStrictUpper.lean#L5-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowApplyEqZeroOfStrictUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.StrictUpperNilpotent

theorem GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper {L : Type} [inst : Field L] {n : ℕ}
    {y : Matrix (Fin n) (Fin n) L} (hy : ∀ (i j : Fin n), j ≤ i → y i j = (0 : L)) :
    ∀ (k : ℕ) (i j : Fin n), (↑j : ℕ) < (↑i : ℕ) + k → (y ^ k) i j = (0 : L) := by sorry
