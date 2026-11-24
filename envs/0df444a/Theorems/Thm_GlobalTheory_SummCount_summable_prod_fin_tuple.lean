-- Prove2me | Theorems.Thm_GlobalTheory_SummCount_summable_prod_fin_tuple
-- name    : GlobalTheory.SummCount.summable_prod_fin_tuple
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:22.574627+00:00
-- url     : https://prove2.me/theorems/a62c8d93-70da-4ec6-bc58-d4a5d90828eb
-- title:
--   Summ Count: summable prod fin tuple
-- statement:
--   The Summ Count construction uses the summable prod fin tuple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SummableRpowOfFibreCardLe.lean#L5-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SummableRpowOfFibreCardLe.lean#L5-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SummableRpowOfFibreCardLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummCount

theorem GlobalTheory.SummCount.summable_prod_fin_tuple {α : Type} {g : α → ℝ} (hg : Summable g) (h0 : ∀ a, 0 ≤ g a)
    (N : ℕ) : Summable fun x : Fin N → α => ∏ i, g (x i) := by sorry
