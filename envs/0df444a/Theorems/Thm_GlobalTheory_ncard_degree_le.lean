-- Prove2me | Theorems.Thm_GlobalTheory_ncard_degree_le
-- name    : GlobalTheory.ncard_degree_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:12:13.965381+00:00
-- url     : https://prove2.me/theorems/44e9167a-da87-43bf-b900-c67f0cb95923
-- title:
--   Global Theory: ncard degree le
-- statement:
--   The Global Theory construction uses the ncard degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MonomialCountAndBinomialEstimates.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MonomialCountAndBinomialEstimates.lean#L18-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
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

theorem GlobalTheory.ncard_degree_le (σ : Type*) [Fintype σ] (k : ℕ) :
    {α : σ →₀ ℕ | α.degree ≤ k}.ncard = (k + Fintype.card σ).choose (Fintype.card σ) := by sorry
