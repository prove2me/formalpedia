-- Prove2me | Theorems.Thm_GlobalTheory_PolynomialNormBound_main
-- name    : GlobalTheory.PolynomialNormBound.main
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:49:47.344949+00:00
-- url     : https://prove2.me/theorems/230add42-9f7b-4dcf-9cc9-0ba3ebc229eb
-- title:
--   Polynomial Norm Bound: main
-- statement:
--   The Polynomial Norm Bound construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ImportsBis.lean#L5-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ImportsBis.lean#L5-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PolynomialNormBound

theorem GlobalTheory.PolynomialNormBound.main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {j m : ℕ}, j ≠ (0 : ℕ) → ¬l ^ m ∣ j →
    ∃ (c : ℤ_[l]), (↑j : ℤ_[l]) * c = (↑l : ℤ_[l]) ^ (m - (1 : ℕ)) := by sorry
