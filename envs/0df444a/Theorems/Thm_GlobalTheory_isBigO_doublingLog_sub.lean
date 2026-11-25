-- Prove2me | Theorems.Thm_GlobalTheory_isBigO_doublingLog_sub
-- name    : GlobalTheory.isBigO_doublingLog_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:57:25.91496+00:00
-- url     : https://prove2.me/theorems/8b1b3e37-4a37-4753-a040-c42b2e14bd82
-- title:
--   Global Theory: is Big O doubling Log sub
-- statement:
--   The Global Theory construction uses the is Big O doubling Log sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoUniformlyOnDoublingLogOfContraction.lean#L145-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoUniformlyOnDoublingLogOfContraction.lean#L145-L153

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

theorem GlobalTheory.isBigO_doublingLog_sub
    (h : (fun x => ε x - (2 : ℂ)⁻¹ • x) =O[𝓝 0] fun x => ‖x‖ ^ 2) :
    (fun x => doublingLog ε x - x) =O[𝓝 0] fun x => ‖x‖ ^ 2 := by sorry
