-- Prove2me | Theorems.Thm_GlobalTheory_tendsto_natDiv_div_self
-- name    : GlobalTheory.tendsto_natDiv_div_self
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:11:40.144885+00:00
-- url     : https://prove2.me/theorems/f8b6be1d-898c-5f00-bef7-906bc0477bce
-- title:
--   Global Theory: tendsto nat Div div self
-- statement:
--   The Global Theory construction uses the tendsto nat Div div self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EventuallyLeAtNearbyIndices.lean#L29-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EventuallyLeAtNearbyIndices.lean#L29-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EventuallyLeAtNearbyIndices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory

theorem GlobalTheory.tendsto_natDiv_div_self (n : ℕ) (hn : 0 < n) :
    Tendsto (fun M : ℕ => ((M / n : ℕ) : ℝ) / M) atTop (𝓝 (1 / n)) := by sorry
