-- Prove2me | Theorems.Thm_GlobalTheory_hasFDerivAt_of_isBigO_sq
-- name    : GlobalTheory.hasFDerivAt_of_isBigO_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:19.323925+00:00
-- url     : https://prove2.me/theorems/dd594464-0da8-4aaf-b53c-aab07a28c414
-- title:
--   Global Theory: has FDeriv At of is Big O sq
-- statement:
--   The Global Theory construction uses the has FDeriv At of is Big O sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoUniformlyOnDoublingLogOfContraction.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoUniformlyOnDoublingLogOfContraction.lean#L31-L35

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

theorem GlobalTheory.hasFDerivAt_of_isBigO_sq {f : E → F} {L : E →L[ℂ] F}
    (h : (fun x => f x - L x) =O[𝓝 0] fun x => ‖x‖ ^ 2) : HasFDerivAt f L 0 := by sorry
