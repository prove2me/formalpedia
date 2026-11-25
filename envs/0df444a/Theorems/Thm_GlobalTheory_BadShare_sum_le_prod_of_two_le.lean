-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_sum_le_prod_of_two_le
-- name    : GlobalTheory.BadShare.sum_le_prod_of_two_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:12.868797+00:00
-- url     : https://prove2.me/theorems/8980087e-a363-50c5-811d-ff09d231b4ac
-- title:
--   Bad Share: sum le prod of two le
-- statement:
--   The Bad Share construction uses the sum le prod of two le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumPrimePowerPartPowSubOneLe.lean#L8-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumPrimePowerPartPowSubOneLe.lean#L8-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumPrimePowerPartPowSubOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare

theorem GlobalTheory.BadShare.sum_le_prod_of_two_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) (h : ∀ i ∈ s, 2 ≤ f i) :
    ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i := by sorry
