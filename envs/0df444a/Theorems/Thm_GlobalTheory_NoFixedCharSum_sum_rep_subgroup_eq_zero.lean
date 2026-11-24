-- Prove2me | Theorems.Thm_GlobalTheory_NoFixedCharSum_sum_rep_subgroup_eq_zero
-- name    : GlobalTheory.NoFixedCharSum.sum_rep_subgroup_eq_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:06.655363+00:00
-- url     : https://prove2.me/theorems/bbc69579-7d9e-4a4e-9492-8787dc203c07
-- title:
--   No Fixed Char Sum: sum rep subgroup eq zero
-- statement:
--   The No Fixed Char Sum construction uses the sum rep subgroup eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumRepSubgroupEqZero.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumRepSubgroupEqZero.lean#L9-L19

import Mathlib
import Definitions.Def_Formalism_JacquetSubsetSums_JacquetSubsetSum
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumRepSubgroupEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NoFixedCharSum

theorem GlobalTheory.NoFixedCharSum.sum_rep_subgroup_eq_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ G V) (N : Subgroup G) [Fintype N]
    (h : ∀ v : V, (∀ n ∈ N, τ n v = v) → v = 0) : ∑ n : N, τ (n : G) = 0 := by sorry
