-- Prove2me | Theorems.Thm_GlobalTheory_TangentRigid_first_order_rigid
-- name    : GlobalTheory.TangentRigid.first_order_rigid
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:40:29.234587+00:00
-- url     : https://prove2.me/theorems/1e6efc91-ff2e-5b54-ba9e-d5c8f7469851
-- title:
--   Tangent Rigid: first order rigid
-- statement:
--   The Tangent Rigid construction uses the first order rigid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FirstOrderRigid.lean#L71-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FirstOrderRigid.lean#L71-L197

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FirstOrderRigid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TangentRigid

theorem GlobalTheory.TangentRigid.first_order_rigid : ∀ (k : Type) [Field k] (m : ℕ) (A B a dA dB : k) (n h dn dh : k[X]), (2 : k) ≠ 0 → (3 : k) ≠ 0 → a ≠ 0 → a ^ 2 = -(2 * (m : k) + 1) → 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 → 12 * A ^ 2 * dA + 54 * B * dB = 0 → n.Monic → h.Monic → n.natDegree = 2 * m + 1 → h.natDegree = m → dn.degree < ((2 * m + 1 : ℕ) : WithBot ℕ) → dh.degree < (m : WithBot ℕ) → IsCoprime n h → (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2 = n ^ 3 + C (a ^ 4 * A) * n * h ^ 4 + C (a ^ 6 * B) * h ^ 6 → (C dA * X + C dB) * (derivative n * h - 2 * n * derivative h) ^ 2 + 2 * (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) * (derivative dn * h + derivative n * dh - 2 * dn * derivative h - 2 * n * derivative dh) = 3 * n ^ 2 * dn + C (a ^ 4 * dA) * n * h ^ 4 + C (a ^ 4 * A) * (dn * h ^ 4 + 4 * n * h ^ 3 * dh) + C (a ^ 6 * dB) * h ^ 6 + 6 * C (a ^ 6 * B) * h ^ 5 * dh → dA = 0 ∧ dB = 0 ∧ dn = 0 ∧ dh = 0 := by sorry
