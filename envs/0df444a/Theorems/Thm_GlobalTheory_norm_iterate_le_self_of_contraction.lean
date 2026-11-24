-- Prove2me | Theorems.Thm_GlobalTheory_norm_iterate_le_self_of_contraction
-- name    : GlobalTheory.norm_iterate_le_self_of_contraction
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:12:47.272142+00:00
-- url     : https://prove2.me/theorems/2820a079-5c98-4363-bd41-46858d2acf38
-- title:
--   Global Theory: norm iterate le self of contraction
-- statement:
--   The Global Theory construction uses the norm iterate le self of contraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoUniformlyOnDoublingLogOfContraction.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoUniformlyOnDoublingLogOfContraction.lean#L63-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {ε : V → V} {r C : ℝ}
omit [NormedSpace ℂ V]

theorem GlobalTheory.norm_iterate_le_self_of_contraction (hc : ∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖)
    {x : V} (hx : x ∈ ball (0 : V) r) (j : ℕ) : ‖ε^[j] x‖ ≤ ‖x‖ := by sorry
