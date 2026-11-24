-- Prove2me | Theorems.Thm_GlobalTheory_tendstoUniformlyOn_doublingLog_of_contraction
-- name    : GlobalTheory.tendstoUniformlyOn_doublingLog_of_contraction
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:22:32.3708+00:00
-- url     : https://prove2.me/theorems/593f59eb-a5da-4bfe-ae3b-ee18d90ee019
-- title:
--   Global Theory: tendsto Uniformly On doubling Log of contraction
-- statement:
--   The Global Theory construction uses the tendsto Uniformly On doubling Log of contraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoUniformlyOnDoublingLogOfContraction.lean#L113-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoUniformlyOnDoublingLogOfContraction.lean#L113-L127

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
variable [CompleteSpace V]

theorem GlobalTheory.tendstoUniformlyOn_doublingLog_of_contraction
    (hc : ∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖)
    (hC0 : 0 ≤ C) (hC : ∀ x ∈ ball (0 : V) r, ‖ε x - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2) :
    TendstoUniformlyOn (fun (j : ℕ) x => (2 : ℂ) ^ j • ε^[j] x) (doublingLog ε) atTop
      (ball 0 r) := by sorry
