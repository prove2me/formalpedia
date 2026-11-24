-- Prove2me | Theorems.Thm_GlobalTheory_ZetaLeft_tendsto_cpow_zero
-- name    : GlobalTheory.ZetaLeft.tendsto_cpow_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:04:56.548882+00:00
-- url     : https://prove2.me/theorems/0aa8dfde-8d93-4447-91b2-21a13e0fd3b9
-- title:
--   Zeta Left: tendsto cpow zero
-- statement:
--   The Zeta Left construction uses the tendsto cpow zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean#L126-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormSubOneMulRiemannZetaLe.lean#L126-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open GlobalTheory GlobalTheory.ZetaLeft

theorem GlobalTheory.ZetaLeft.tendsto_cpow_zero {c : ℂ} (hc : c.re < 0) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1 : ℝ) : ℂ) ^ c) atTop (𝓝 0) := by sorry
