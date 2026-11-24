-- Prove2me | Theorems.Thm_GlobalTheory_isBigO_sub_linear_sq_of_analyticAt
-- name    : GlobalTheory.isBigO_sub_linear_sq_of_analyticAt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:57:35.336884+00:00
-- url     : https://prove2.me/theorems/b172ee0c-1d84-4ae5-8981-d778c304dc6f
-- title:
--   Global Theory: is Big O sub linear sq of analytic At
-- statement:
--   The Global Theory construction uses the is Big O sub linear sq of analytic At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoUniformlyOnDoublingLogOfContraction.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoUniformlyOnDoublingLogOfContraction.lean#L14-L24

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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem GlobalTheory.isBigO_sub_linear_sq_of_analyticAt {f : E → F} {L : E →L[ℂ] F} (hf : AnalyticAt ℂ f 0)
    (h0 : f 0 = 0) (hL : HasFDerivAt f L 0) :
    (fun x => f x - L x) =O[𝓝 0] fun x => ‖x‖ ^ 2 := by sorry
