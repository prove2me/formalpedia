-- Prove2me | Theorems.Thm_GlobalTheory_natCard_degree_le
-- name    : GlobalTheory.natCard_degree_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:12:13.412116+00:00
-- url     : https://prove2.me/theorems/5b5288f8-8333-4ceb-a366-deca961d232f
-- title:
--   Global Theory: nat Card degree le
-- statement:
--   The Global Theory construction uses the nat Card degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MonomialCountAndBinomialEstimates.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MonomialCountAndBinomialEstimates.lean#L38-L42

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

theorem GlobalTheory.natCard_degree_le (σ : Type*) [Fintype σ] (k : ℕ) :
    Nat.card {α : σ →₀ ℕ // α.degree ≤ k} = (k + Fintype.card σ).choose (Fintype.card σ) := by sorry
