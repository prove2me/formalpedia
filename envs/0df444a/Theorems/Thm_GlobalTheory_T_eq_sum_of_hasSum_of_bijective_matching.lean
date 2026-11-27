-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_sum_of_hasSum_of_bijective_matching
-- name    : GlobalTheory.T.eq_sum_of_hasSum_of_bijective_matching
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T06:04:42.751643+00:00
-- url     : https://prove2.me/theorems/ac470705-258d-4f00-a954-054141c0859f
-- title:
--   T: eq sum of has Sum of bijective matching
-- statement:
--   The T construction uses the eq sum of has Sum of bijective matching property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumEqSumOfMatchingFamilyStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumEqSumOfMatchingFamilyStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumEqSumOfMatchingFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumEqSumOfMatchingFamilyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eq_sum_of_hasSum_of_bijective_matching : ∀ (C : Type 1) (n : ℕ) (m : C → ℕ) (t : C → ℂ) (m' : Fin n → ℕ) (c : Fin n → ℂ) (R : C → Fin n → Prop) (s : ℂ), HasSum (fun x => (m x : ℂ) * t x) s → (∀ x, m x ≠ 0 → t x ≠ 0 → ∃ i, R x i) → (∀ i, m' i ≠ 0 → ∃ x, R x i) → (∀ x i, R x i → m x = m' i ∧ t x = c i) → (∀ x i j, R x i → R x j → i = j) → (∀ x y i, R x i → R y i → x = y) → s = ∑ i, (m' i : ℂ) * c i := by sorry
