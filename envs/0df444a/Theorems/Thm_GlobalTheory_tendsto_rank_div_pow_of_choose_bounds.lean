-- Prove2me | Theorems.Thm_GlobalTheory_tendsto_rank_div_pow_of_choose_bounds
-- name    : GlobalTheory.tendsto_rank_div_pow_of_choose_bounds
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:00.738323+00:00
-- url     : https://prove2.me/theorems/c688d05b-22c8-4e2c-82e7-6bb57c4488b2
-- title:
--   Global Theory: tendsto rank div pow of choose bounds
-- statement:
--   The Global Theory construction uses the tendsto rank div pow of choose bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TendstoRankDivPowOfChooseBounds.lean#L19-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TendstoRankDivPowOfChooseBounds.lean#L19-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TendstoRankDivPowOfChooseBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory

theorem GlobalTheory.tendsto_rank_div_pow_of_choose_bounds (D e δ : ℕ) (r : ℕ → ℕ) (he : 0 < e)
    (h : ∀ s : ℕ, s < e → ∃ c c' : ℕ, ∀ q : ℕ,
      δ * (q + D).choose D ≤ r (e * (q + c) + s) ∧ r (e * q + s) ≤ δ * (q + c' + D).choose D) :
    Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop
      (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by sorry
