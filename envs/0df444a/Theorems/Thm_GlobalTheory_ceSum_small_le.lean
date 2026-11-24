-- Prove2me | Theorems.Thm_GlobalTheory_ceSum_small_le
-- name    : GlobalTheory.ceSum_small_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:08:02.928863+00:00
-- url     : https://prove2.me/theorems/f476fc8b-817e-4753-985f-ee89093df180
-- title:
--   Global Theory: ce Sum small le
-- statement:
--   The Global Theory construction uses the ce Sum small le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CmValuesExponentLogSumLe.lean#L29-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CmValuesExponentLogSumLe.lean#L29-L46

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CmValuesExponentLogSumLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory

theorem GlobalTheory.ceSum_small_le (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) (n : ℕ) :
    ∑ l ∈ S, (if l ≤ n then Real.log l else 0) ≤ n * Real.log 4 := by sorry
