-- Prove2me | Theorems.Thm_GlobalTheory_ncard_degree_eq
-- name    : GlobalTheory.ncard_degree_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:12:11.728843+00:00
-- url     : https://prove2.me/theorems/aab7266f-1bd7-48b0-865a-e1a093c6a819
-- title:
--   Global Theory: ncard degree eq
-- statement:
--   The Global Theory construction uses the ncard degree eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MonomialCountAndBinomialEstimates.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MonomialCountAndBinomialEstimates.lean#L12-L16

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

theorem GlobalTheory.ncard_degree_eq (σ : Type*) [Fintype σ] (a : ℕ) :
    {α : σ →₀ ℕ | α.degree = a}.ncard = (a + Fintype.card σ - 1).choose a := by sorry
