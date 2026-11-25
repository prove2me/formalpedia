-- Prove2me | Theorems.Thm_GlobalTheory_T_card_perm_partition_parts_mul_centralizer
-- name    : GlobalTheory.T.card_perm_partition_parts_mul_centralizer
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:59:17.890352+00:00
-- url     : https://prove2.me/theorems/4cdce85e-3b7f-544d-bea6-39f8acf69fd0
-- title:
--   T: card perm partition parts mul centralizer
-- statement:
--   The T construction uses the card perm partition parts mul centralizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPermPartitionPartsMulCentralizerStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPermPartitionPartsMulCentralizerStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPermPartitionPartsMulCentralizer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPermPartitionPartsMulCentralizerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_perm_partition_parts_mul_centralizer : ∀ (N : ℕ) (μ : Multiset ℕ), (∀ d ∈ μ, 0 < d) → μ.sum = N → (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ).card * ∏ d ∈ μ.toFinset, (d ^ μ.count d * (μ.count d).factorial) = N.factorial := by sorry
