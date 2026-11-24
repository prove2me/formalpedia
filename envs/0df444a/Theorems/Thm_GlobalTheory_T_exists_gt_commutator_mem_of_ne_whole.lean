-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_gt_commutator_mem_of_ne_whole
-- name    : GlobalTheory.T.exists_gt_commutator_mem_of_ne_whole
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:36:35.771071+00:00
-- url     : https://prove2.me/theorems/baa30490-0dc4-4eab-bbb4-d4e22cd22b49
-- title:
--   T: exists gt commutator mem of ne whole
-- statement:
--   The T construction uses the exists gt commutator mem of ne whole property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLtCommutatorMemOfNeTopStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLtCommutatorMemOfNeTopStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLtCommutatorMemOfNeTop
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLtCommutatorMemOfNeTopStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI GlobalTheory.BrauerZero
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_gt_commutator_mem_of_ne_whole : ∀ {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] (K : Subgroup G), K ≠ ⊤ → ∃ A : Subgroup G, K < A ∧ ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ K := by sorry
