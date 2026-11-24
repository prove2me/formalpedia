-- Prove2me | Theorems.Thm_GlobalTheory_NormDetIndex_norm_det_eq_norm_index
-- name    : GlobalTheory.NormDetIndex.norm_det_eq_norm_index
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:34:26.609272+00:00
-- url     : https://prove2.me/theorems/7630a55e-405c-48e4-8616-a338940960c8
-- title:
--   Norm Det Index: norm det eq norm index
-- statement:
--   The Norm Det Index construction uses the norm det eq norm index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NormCardQuotientSpan.lean#L24-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NormCardQuotientSpan.lean#L24-L62

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

theorem GlobalTheory.NormDetIndex.norm_det_eq_norm_index (l : ℕ) [Fact (Nat.Prime l)] {κ : Type} [Fintype κ]
    [DecidableEq κ] (M : Matrix κ κ ℤ_[l]) (hM : M.det ≠ 0) :
    ‖M.det‖ = ‖((LinearMap.range M.mulVecLin).toAddSubgroup.index : ℚ_[l])‖ := by sorry
