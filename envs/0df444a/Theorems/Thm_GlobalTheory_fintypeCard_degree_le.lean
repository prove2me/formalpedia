-- Prove2me | Theorems.Thm_GlobalTheory_fintypeCard_degree_le
-- name    : GlobalTheory.fintypeCard_degree_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:51.523734+00:00
-- url     : https://prove2.me/theorems/41dad8e5-356b-49b5-ab63-d0b2cc37a973
-- title:
--   Global Theory: fintype Card degree le
-- statement:
--   The Global Theory construction uses the fintype Card degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MonomialCountAndBinomialEstimates.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MonomialCountAndBinomialEstimates.lean#L44-L49

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

theorem GlobalTheory.fintypeCard_degree_le (σ : Type*) [Fintype σ] (k : ℕ)
    [Fintype {α : σ →₀ ℕ // α.degree ≤ k}] :
    Fintype.card {α : σ →₀ ℕ // α.degree ≤ k} =
      (k + Fintype.card σ).choose (Fintype.card σ) := by sorry
