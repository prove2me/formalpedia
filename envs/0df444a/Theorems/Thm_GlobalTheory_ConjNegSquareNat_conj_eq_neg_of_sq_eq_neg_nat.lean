-- Prove2me | Theorems.Thm_GlobalTheory_ConjNegSquareNat_conj_eq_neg_of_sq_eq_neg_nat
-- name    : GlobalTheory.ConjNegSquareNat.conj_eq_neg_of_sq_eq_neg_nat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:25:40.410565+00:00
-- url     : https://prove2.me/theorems/7ed8c08e-a5a3-40ae-8246-2d829b3aadb1
-- title:
--   Conj Neg Square Nat: conj eq neg of sq eq neg nat
-- statement:
--   The Conj Neg Square Nat construction uses the conj eq neg of sq eq neg nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ConjEqNegOfSqEqNegNat.lean#L5-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ConjEqNegOfSqEqNegNat.lean#L5-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ConjEqNegOfSqEqNegNat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConjNegSquareNat

theorem GlobalTheory.ConjNegSquareNat.conj_eq_neg_of_sq_eq_neg_nat {z : ℂ} {d : ℕ} (hd : (0 : ℕ) < d)
    (h : z ^ (2 : ℕ) = -(↑d : ℂ)) : (starRingEnd ℂ : ℂ → ℂ) z = -z := by sorry
