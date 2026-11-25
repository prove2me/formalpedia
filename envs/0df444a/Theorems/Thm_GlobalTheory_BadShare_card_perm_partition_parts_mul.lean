-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_card_perm_partition_parts_mul
-- name    : GlobalTheory.BadShare.card_perm_partition_parts_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:59:39.878814+00:00
-- url     : https://prove2.me/theorems/8e04e09f-061a-5f39-9e36-df6e109131f3
-- title:
--   Bad Share: card perm partition parts mul
-- statement:
--   The Bad Share construction uses the card perm partition parts mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPermPartitionPartsMulCentralizer.lean#L20-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPermPartitionPartsMulCentralizer.lean#L20-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPermPartitionPartsMulCentralizer
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

theorem GlobalTheory.BadShare.card_perm_partition_parts_mul :
    ∀ (N : ℕ) (μ : Multiset ℕ), (∀ d ∈ μ, 0 < d) → μ.sum = N →
      (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ).card *
        ∏ d ∈ μ.toFinset, (d ^ μ.count d * (μ.count d).factorial) = N.factorial := by sorry
