-- Prove2me | Theorems.Thm_GlobalTheory_splitHeight_summable_pi_prod
-- name    : GlobalTheory.splitHeight_summable_pi_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T06:02:41.085122+00:00
-- url     : https://prove2.me/theorems/4c5e58db-b72e-43c6-b34b-642a65b23930
-- title:
--   Global Theory: split Height summable pi prod
-- statement:
--   The Global Theory construction uses the split Height summable pi prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SplitHeightSummableExpNegAbs.lean#L9-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SplitHeightSummableExpNegAbs.lean#L9-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SplitHeightSummableExpNegAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
open Finset

theorem GlobalTheory.splitHeight_summable_pi_prod {ι : Type} [Fintype ι] {α : ι → Type} {f : ∀ i, α i → ℝ}
    (h0 : ∀ i x, 0 ≤ f i x) (hf : ∀ i, Summable (f i)) :
    Summable fun n : ∀ i, α i => ∏ i, f i (n i) := by sorry
