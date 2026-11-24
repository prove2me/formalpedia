-- Prove2me | Theorems.Thm_GlobalTheory_T_tendsto_div_pow_of_choose_bounds
-- name    : GlobalTheory.T.tendsto_div_pow_of_choose_bounds
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:59:38.432808+00:00
-- url     : https://prove2.me/theorems/4a9ff5a4-be20-4763-ab36-f0b8243517c3
-- title:
--   T: tendsto div pow of choose bounds
-- statement:
--   The T construction uses the tendsto div pow of choose bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TendstoRankDivPowOfChooseBoundsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TendstoRankDivPowOfChooseBoundsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TendstoRankDivPowOfChooseBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TendstoRankDivPowOfChooseBoundsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.tendsto_div_pow_of_choose_bounds : ∀ (D e δ : ℕ) (r : ℕ → ℕ), 0 < e → (∀ s : ℕ, s < e → ∃ c c' : ℕ, ∀ q : ℕ, δ * (q + D).choose D ≤ r (e * (q + c) + s) ∧ r (e * q + s) ≤ δ * (q + c' + D).choose D) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by sorry
