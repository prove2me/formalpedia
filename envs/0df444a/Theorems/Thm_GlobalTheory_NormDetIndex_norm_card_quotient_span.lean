-- Prove2me | Theorems.Thm_GlobalTheory_NormDetIndex_norm_card_quotient_span
-- name    : GlobalTheory.NormDetIndex.norm_card_quotient_span
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:34:20.68084+00:00
-- url     : https://prove2.me/theorems/168bc62e-42e1-4d83-bc5a-53230ce18dba
-- title:
--   Norm Det Index: norm card quotient span
-- statement:
--   The Norm Det Index construction uses the norm card quotient span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NormCardQuotientSpan.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NormCardQuotientSpan.lean#L7-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NormCardQuotientSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormDetIndex
open Module Submodule

theorem GlobalTheory.NormDetIndex.norm_card_quotient_span (l : ℕ) [Fact (Nat.Prime l)] {x : ℤ_[l]} (hx : x ≠ 0) :
    ‖((Nat.card (ℤ_[l] ⧸ Ideal.span ({x} : Set ℤ_[l])) : ℕ) : ℚ_[l])‖ = ‖x‖ := by sorry
